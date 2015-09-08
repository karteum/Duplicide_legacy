#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Duplicide - a tool to detect duplicate files and dirs !
# Author: Adrien Demarez (adrien.demarez@free.fr)
# Version: 20140119
# License: GPLv3
# Usage: python duplicide.py dir1/ [dir2] [...]
#
# Goals:
#   - detect duplicate files (like fslint and any other similar tools), as quickly as possible i.e. without performing hash/compare unnecessarily and without unnecessary I/O, and with a proper progressbar
#   - detect duplicate dirs (i.e. don't output files/dirs as a result if the whole parent dir is itself a duplicate).
#   - don't output pseudo-duplicate that are hard links. Process by sorted inode in order to limit HDD seeks (like fslint in https://code.google.com/p/fslint/source/browse/trunk/fslint/findup )
#   - can process hash on a small fraction of the files instead of the whole file in order to speedup tests (at the expense of reliability / risk of false positive => human double-check is necessary !). In practical situations (99% of the time), identical size + identical crc32 on fist kbytes is OK...
#   - it's only a detection program. What to do with duplicates (e.g. delete them or making hard links or symlinks or any other idea) is up to the user or calling script/program.
#
# TODO:
#   - handle not only identical dirs, but also "similar" ones
#   - handle case where a "clean reference dir" is given, so that it outputs the duplicate files/dirs outside of this reference (i.e. that can be deleted) and the ones that have to be backup'ed inside the reference.
#   - allow to serialize the computed hashes
#   - clean-up code, which is currently spaghetti-like. I'd like to isolate more the function+data they operate on. Currently, nearly all functions do something on ~all the global variables
#
# DISCLAIMER: as it is mentioned in the GPLv3 (but I prefer to repeat it): there is no warranty of any kind with this tool. It is not bug-free. Use it at your own risk !
#             Among other things (and not limited to this), it may output wrong results such as false positive and therefore it requires human double-check before you delete any (supposed) duplicate data it outputs.
#             I am not responsible for any data-loss caused directly or indirectly by this program !

import os,sys,mmap,stat
import zlib #import binascii
import hashlib #import md5
import filecmp
from collections import defaultdict
import time
import fnmatch # re ?
#import argparse
#import platform
from multiprocessing import Process, Array
import random

# TODO: allow disjoint chunks ? allow rdiff-like sliding-window CRC ?
def checksum_file(filename, size=-1, hashalgo='crc32', chunk=-1): # (1<<12)
    # This function used to rely on mmap(), however this is an issue for big files on 32 bits machines
    #~ MAXMAPSIZE = 1<<(int(platform.architecture()[0][0:2])-1) - 1<<20  # FIXME: it also assumes number of bits takes 2 digits, so it does not work for 128bit platforms ! :). The 1<<20 is to take a small margin.
    """Performs a hash (CRC32, or any other supported by hashlib such as MD5 or SHA256) on the first [size] bytes of the file [filename]"""
    #return random.randint(0,1<<32-1)
    maxsize = int(os.stat(filename).st_size) - 1 # FIXME: why -1 ?
    readsize = (size > 0) and min(maxsize, size) or maxsize
    readchunk = (chunk > 0) and min(chunk, readsize) or readsize
    with open(filename,'r') as fh:
        readoffset = 0
        #~ map = mmap.mmap(fh.fileno(), realsize, mmap.MAP_PRIVATE, mmap.PROT_READ)
        #~ map = mmap.mmap(fh.fileno(), CHUNK, access=mmap.ACCESS_READ, offset=readoffset)
        if (hashalgo == "crc32" or hashalgo == "adler32"):
            crcfun = (hashalgo == "adler32") and zlib.adler32 or zlib.crc32 # or binascii.crc32
            mycrc = 0
            while (readoffset < readsize):
                buf = fh.read(readchunk)
                mycrc = crcfun(buf, mycrc)
                readoffset += len(buf)
            return hex(mycrc & 0xffffffff) #~ hex(zlib.crc32(map[0:realsize]) & 0xffffffff)
        else:
            digest = hashlib.new(hashalgo) # or md5.new()
            while (readoffset < readsize): # while len(buf) > 0 ?
                buf = fh.read(readchunk)
                digest.update(buf) #~ (map[0:realsize])
                readoffset += len(buf)
            return digest.hexdigest()
        #~ map.close()

def checksum_props(props, hashalgo='crc32'):
    """Returns a hash from the 'properties' of a directory (size and MD5 of child files and subdirs, etc.). If two dirs have the same 'md5props', they will be considered as duplicates"""
    if (hashalgo == "crc32"):
        result = hex(zlib.crc32(str(props)) & 0xffffffff) # or binascii.crc32
    else:
        digest = hashlib.new(hashalgo)
        digest.update(str(props))
        result = digest.hexdigest()
    return result

class progresswalk:
    """Progress indicator for os.walk""" # The implementation may look complex, but it's because it tries to put the right "weigth" to dirs according to how deep they are in the filesystem
    def __init__(self, init_path):
        self.init_path = init_path
        self.init_depth = init_path.count('/')
        self.numdirs = [0+0j]

    def update(self, dir, dirs):
        # numdirs[] is processed as a "polynom". It is using complex numbers in order to avoid using 2 lists: real part is total number of dirs, and imag part is number of processed dirs
        current_depth = dir.count('/') - self.init_depth
        if len(self.numdirs) < current_depth+2:
            self.numdirs.append(0+0j)
        self.numdirs[current_depth+1] += len(dirs)
        walkedRatio=0
        # compact the "polynom" numdirs with each "digit" in 0-9, and fit it into a "normal" integer
        for i in range(1, len(self.numdirs)-2): # [1:len(numdirs)-2] because the first value is 0 and the last value may be 0, and we want to avoid division by 0 !
            walkedRatio = walkedRatio*10 + int((9*self.numdirs[i].imag)/self.numdirs[i].real)
        completion = (100*walkedRatio) / (10**(len(self.numdirs)-3))
        self.numdirs[current_depth] += 1j
        #sys.stderr.write("\rScanning: [%d %%]   %s" % (completion,str(self.numdirs))) # self.init_path
        sys.stderr.write("\rScanning: [%d %%]" % (completion,)) # self.init_path

class dupcontext:
    def __init__(self):
        # FIXME: replace all lists by sets ? Put those global variables into a class ?
        # For files
        self.sizeinodes = defaultdict(list) ;  self.inodessizes = defaultdict(int)
        self.inodesfiles = defaultdict(list) ; self.filesinodes = defaultdict(int)
        self.hashinodes = defaultdict(list) ;  self.inodeshash = {}

        # For dirs : for each dir key, dirsAttrsOnFiles[key] (resp. dirsAttrsOnSubdirs for subdirs instead of subfiles) is a list of entries. values[0] is the number of files, values[1] is the size of the dir, then values[2:..] contains the file sizes, then we also push later computed hashes for files
        self.dirsAttrsOnFiles = {} ;        self.dirsAttrsOnSubdirs = {}
        self.sizedirs = defaultdict(list) ; self.dirsizes = defaultdict(int)
        self.hashdirs = defaultdict(list) ; self.dirshash = {}
        self.roots = []

        self.dupresultsD = defaultdict(list) ; self.dupresultsF = defaultdict(list) # the result
        #incdirs = defaultdict(list) ; incfiles = defaultdict(list)

    def __add_file(self, dir, file):
        path = dir + "/" + file
        if not os.path.exists(path) or not os.access(path, os.R_OK):
            # Skip broken symlinks, and cases where we do not have access rights. TODO: check whether access rights are tied to inode or path
            sys.stderr.write("Unable to access %s!\n" % (path,))
            return 0
        filestat = os.lstat(path)
        size = int(filestat.st_size)
        if (not option_include_nullfiles and size == 0) or (not option_include_nonregfiles and not stat.S_ISREG(filestat.st_mode)): # not os.path.isfile(path):
            # FIXME: include those files in another db, so that comparing dirs will not omit them ? or just serialize the whole stat().st_mode in dirsAttrsOnSubdirs ?
            return 0
        self.dirsAttrsOnFiles[dir].append(size) # BUGFIX: case where same number of subfiles, different file sizes but same sum(sizes), different filemd5
        fakeino = (filestat.st_dev << 32) | filestat.st_ino  # "fake" inode (merging dev and inode in order to get a unique ID. FIXME: maybe st_dev can change across reboots or device insertion/removal ? In that case, it would be dangerous to serialize/deserialize and mix loaded info with new scanned info ?
        if option_include_hardlinks or not fakeino in self.inodesfiles:
            self.sizeinodes[size].append(fakeino) # FIXME: use set instead of list to ensure unicity !
        else:
            print "skipping " + path  # FIXME: is it really skipped ? what should happen to the following lines ?
        self.filesinodes[path] = fakeino
        self.inodesfiles[fakeino].append(path)
        self.inodessizes[fakeino] = size
        return size

    # ftw() in the whole dir structure and compute hash on the relevant files and dirs
    def scandir(self, init_path):
        """Add a dir to the scan context"""
        self.roots.append(init_path)
        progress = progresswalk(init_path)
        for (dir, dirs, files) in os.walk(init_path):
            progress.update(dir, dirs)
            for excludetest in option_excludelist:
                if fnmatch.fnmatch(dir, excludetest):
                    continue

            # Processing current dir : compute dir size, and store file sizes into sizefiles
            dirsize = 0
            self.dirsAttrsOnFiles[dir] = [len(files)]
            self.dirsAttrsOnSubdirs[dir] = [len(dirs)]
            for file in files:
                dirsize += self.__add_file(dir, file)

            # Increment all parents dir size with current dir size
            while(dirsize > 0 and dir != init_path and dir != '/'):
                self.dirsizes[dir] += dirsize
                dir = os.path.dirname(dir)

        # Reverse sizes for dirs
        for (dir,size) in self.dirsizes.iteritems():
            self.sizedirs[size].append(dir)
            self.dirsAttrsOnSubdirs[dir][0] |= size << 32 #dirsAttrsOnSubdirs[dir].append(size)

    def loadfrom(self, file):
        """Load context from file"""
        pass

    def saveto(self, file):
        """Save context to file"""
        pass

    def process(self):
        """Launch analyze of the context in order to find duplicate dirs and files"""
        self.__compute_fileshash()
        self.__compute_dirshash()
        self.__compute_duplicates()

    def __compute_fileshash(self):
        # See which files need to be looked at for computing hash (i.e. only if several files have the same size)
        # Compute hash for files (sorting by inode in order to use disk internal buffering/readahead and avoid disk seeks)
        # TODO: put this in a function and use multithreading for the computation ? (N.B. is it I/O or CPU bounded, especially in case of crc32 on the first 64k ?)
        # needs: sizeinodes, inodessizes, inodesfiles, inodeshash, hashinodes, dirsAttrsOnFiles
        inodes_tohash = []
        for inodelist in filter(lambda x: len(x)>1, self.sizeinodes.values()):
            inodes_tohash.extend(inodelist)

        i = 0 ; total = len(inodes_tohash)
        for inode in sorted(inodes_tohash):
            curr_size = self.inodessizes[inode]
            file0 = self.inodesfiles[inode][0] # N.B. the access rights and other properties are identical to all hard links as they are bound to the inode
            curr_hash = "%s_%s" % (curr_size, checksum_file(file0, size=SIZE_CKSUM, hashalgo='md5')) # adler32
            for file in self.inodesfiles[inode]:
                self.dirsAttrsOnFiles[os.path.dirname(file)].append(curr_hash)
            #~ if not inode in self.inodeshash.keys():
            self.hashinodes[curr_hash].append(inode)
            self.inodeshash[inode] = curr_hash
            completion = (100*i)/total
            sys.stderr.write("\rComputing checksums for dev/inode 0x%x: [%d %%]" % (inode, completion))
            i+=1

    def __isdup(self, path):
        return self.inodeshash[self.filesinodes[path]] > 1

    def __numdups(self, dupentry):
        # Returns how many duplicate siblings this directory has
        if not dupentry in self.dirshash: return -1
        return len(self.hashdirs[self.dirshash[dupentry]])

    def __bestParent(self, currentdir):
        parentdir = os.path.dirname(currentdir)
        while (parentdir in self.dirshash and len(self.hashdirs[self.dirshash[parentdir]])>1):
            #incdirs[parentdir].append(currentdir)
            currentdir = parentdir
            parentdir = os.path.dirname(parentdir)
        return currentdir #dirshash[currentdir] # FIXME: hashdirs[] ?

    def __compute_dirshash(self):
        # Compute "hash" for relevant dirs
        # FIXME: I would like to avoid another os.walk, however doing it bottom-up is the easiest (though not best) way to compute hashes for leaf dirs first (hopefully the previous os.walk() is still in the OS cache despite the more recent computation of file checksums...)
        # needs: init_path, sizedirs, dirsizes, dirsAttrsOnSubdirs, dirsAttrsOnFiles, dirshash, hashdirs
        for init_path in self.roots:
            for (dir, dirs, files) in os.walk(init_path, topdown=False):
                # If any subdir or subfile wasn't added to the properties, it means it is not a duplicate, and therefore the current dir is not a duplicate
                if(len(self.sizedirs[self.dirsizes[dir]])>1 and len(self.dirsAttrsOnSubdirs[dir])==(1+len(dirs)) and len(self.dirsAttrsOnFiles[dir])==(1+len(files))):
                    tmp_props = sorted(self.dirsAttrsOnFiles[dir])
                    tmp_props.extend(sorted(self.dirsAttrsOnSubdirs[dir]))
                    curr_hash = "%s_%s" % (self.dirsizes[dir], checksum_props(tmp_props, hashalgo='md5')) # crc32
                    self.dirshash[dir] = curr_hash
                    self.hashdirs[curr_hash].append(dir)
                    self.dirsAttrsOnSubdirs[os.path.dirname(dir)].append(curr_hash)
                #~ else:
                    #~ print "Skipping %s %d %d %d %s" % (dir, len(dirsAttrsOnSubdirs[dir]), len(dirs), len(sizedirs[dirsizes[dir]]), str(dirsAttrsOnSubdirs[dir]))

    def __compute_duplicates(self):
        #~ dupdirset = set()
        for dupdirs in filter(lambda x: len(x)>1, self.hashdirs.values()):
            for currentdir in dupdirs:
                parentdir = self.__bestParent(currentdir)
                if not parentdir in self.dupresultsD[self.dirshash[parentdir]]:
                    self.dupresultsD[self.dirshash[parentdir]].append(parentdir)
                #~ dupdirset.add(parentdir)

        for inodelist in filter(lambda x: len(x)>1, self.hashinodes.values()):
            for dupinode in inodelist:
                #~ if len(self.inodesfiles[dupinode]) > 1:
                    #~ print "hard link" + str(self.inodesfiles[dupinode])
                for dupfile in self.inodesfiles[dupinode]: # FIXME: no need for a for() loop since we already discarded hard links !
                    currentdir = os.path.dirname(dupfile)
                    if not currentdir in self.dirshash or len(self.hashdirs[self.dirshash[currentdir]]) < 2:
                        self.dupresultsF[self.inodeshash[dupinode]].append(dupinode)
                        # TODO: compute hashset() for the dir, to compare with peers and be able to eventually say dirA > dirB...
        # TODO: double-check with filecmp.cmp()

    def __print_duplicates(self, dupresults, files=False):
        # TODO: allow mixed files/dirs output
        resultsorted = {}
        for k,v in dupresults.iteritems():
            resultsorted[int(k.partition('_')[0])] = v
        for k in sorted(resultsorted.keys()):
            sys.stdout.write("%d kB * %d: " % ((k>>10)+1, len(resultsorted[k])))
            if(files==True):
                for inode in resultsorted[k]:
                    sys.stdout.write(str(self.inodesfiles[inode]) + ", ")
                print ""
            else:
                print str(resultsorted[k])

    def print_dupdirs(self):
        """Print duplicate dirs found in the context"""
        self.__print_duplicates(self.dupresultsD)

    def print_dupfiles(self):
        """Print duplicate files found in the context"""
        self.__print_duplicates(self.dupresultsF, True)

# Options
SIZE_CKSUM = (1<<16)
option_include_nullfiles = False
option_include_nonregfiles = False # FIXME: 'True' case is not handled yet !
option_include_hardlinks = False
option_excludelist = []

if __name__ == "__main__":
    #parser = argparse.ArgumentParser(description='Detects all the duplicate files and dirs')
    #parser.add_argument('-f', action='store_true', default=False, help="display duplicate files")
    #args=parser.parse_args()
    #print args
    context = dupcontext()
    if len(sys.argv)==1:
        print "Usage: duplicide dir1/ [dir2/ dir3/ ...]"
        sys.exit (0)
    for arg in sys.argv:
        init_path = arg.rstrip('/')
        context.scandir(init_path)
    context.process()
    print "\nDuplicate dirs:"
    context.print_dupdirs()
    print "\nDuplicate files:"
    context.print_dupfiles()
