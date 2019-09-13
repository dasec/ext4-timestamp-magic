#!/usr/bin/env python3
# Hide and Restore Data in Filesystem Timestamps within Ext4 Filesystem
#
# Author: Thomas Goebel
#
import unireedsolomon
import reedsolo
import time
import os
import sys
import math
import hashlib
import random
from sys import byteorder, stdin, stdout, stderr
from posix import listdir
import subprocess
import shlex
from multiprocessing import Pipe
from subprocess import PIPE
from getpass import _raw_input
from io import BytesIO
from Crypto.Cipher import ARC4
from Crypto import Random
from _stat import ST_INO
from os.path import join, abspath, getatime, getmtime
from argparse import ArgumentParser
import binascii

# Fixed Size
MOD_TIME_OFFSET = 136  # 0x88 __le32 i_mtime_extra
ACC_TIME_OFFSET = 140  # 0x8C __le32 i_atime_extra
CR_TIME_OFFSET = 148  # 0x94 __le32 i_crtime_extra


def bytes2int(b):
    res = 0
    print(b)
    for x in b[::-1]:
        res = (res << 8) + x
    return res


def readBmpFile():
    with open("/mount_ext/Andy.bmp", "rb") as f:
        f.seek(18)

        # print("Breite:", bytes2int(f.read(4)), "px")
        print("Breite:", int.from_bytes(f.read(4), byteorder='little'), "px")
        print("Höhe:", int.from_bytes(f.read(4), byteorder='little'), "px")
        f.seek(2, 1)
        print("Farbtiefe:", int.from_bytes(f.read(2), byteorder='little'), "px")



def shiftByteArrayLeft(chunk, shift):
    chunk[0] = (chunk[0] << shift) & 255
    for i in range(1, len(chunk)):
        chunk[i - 1] = (chunk[i-1] | (chunk[i] >> (8-shift))) & 255
        chunk[i] = (chunk[i] << shift) & 255
    return chunk

def shiftByteArrayRight(chunk, shift):
    chunk[-1] >>=  shift
    for i in reversed(range(0, len(chunk)-1)):
        chunk[i + 1] = (chunk[i + 1] | (chunk[i] << (8 - shift))) & 255
        chunk[i] = (chunk[i] >> shift) & 255
    return chunk

def insertBitGap(chunk):
    part1 = chunk[0:3]
    part2 = chunk[3:]
    if part2 != (b''):
        if len(part2) < 4:
            x = 4 - len(part2)
            part2 = bytearray(b''.join([part2, (0).to_bytes(x, byteorder='big')]))

        part2 = shiftByteArrayRight(part2, 2)
        part2[0] = part2[0] | ((part1[2] << 6) & 255)
    else:
        part2 = bytearray(b'')
        part2.append((part1[2] << 6) & 255)
    part1[2] &= int('11111100', 2) # part1 maskieren
    return part1 + part2


def splitDataIntoChunks13(dataEncoded):
    chunkSize = 13
    # first get total size of data to get hidden
    # then divide by total available amount of space per inode (6,5 bytes, due to 2* 2 zero bits per inode)
    # every 256th chunk entry contains message length (due to index byte overflow at 0xff)
    # so that each 255 out of 256 inodes are available to hide data
    
    sizeInBytes = len(dataEncoded)
    numberOfUsedInodes = math.ceil(sizeInBytes / 6.5)
    numberOfUsedInodes += (numberOfUsedInodes // 255)
    numberOfUsedInodes += 1 #first entry: offsetInode

    print("Größe der Datei:", sizeInBytes, "\nVerfügbarer Speicher pro Inode:", chunkSize,
          "\nAnzahl Chunks:", numberOfUsedInodes)

    chunks = []
    chunksWithIndexByte = []
    encryptedChunks = []
    shiftedChunks = []


    # create multiple 7 byte chunks with 1 byte overlap (for subsequent shift operation)
    # i.e. last byte of chunk0 matches first byte of chunk1 and so on
    for i in range(0, sizeInBytes, chunkSize):
        chunks.append(dataEncoded[i:(i+7)])
        if len(dataEncoded[(i+6):(i+13)]) != 0:
            chunks.append(dataEncoded[(i+6):(i+13)])


    # insert index bytes (one per inode / 7 bytes chunk) and insert repeating bytes with message length every 256 chunks
    index = 0
    for element in chunks:
        if index == 0:
            # index byte with stored number of used inodes and size in bytes
            # last byte remains empty due to the two bits of the date which needs to be empty
            temp = b''.join([index.to_bytes(1, byteorder='big'),
                             numberOfUsedInodes.to_bytes(2, byteorder='big'), (0).to_bytes(1, byteorder='big'),
                             # numberOfUsedInodes.to_bytes(3, byteorder='big'),
                             sizeInBytes.to_bytes(3, byteorder='big'), (0).to_bytes(1, byteorder='big')])
                             # sizeInBytes.to_bytes(4, byteorder='big')])
            chunksWithIndexByte.append(bytearray(temp))
            index += 1

        temp = b''.join([index.to_bytes(1, byteorder='big'), element])
        index = (index + 1) % 256
        chunksWithIndexByte.append(bytearray(temp))


    for element in chunksWithIndexByte:
        element = bytes(element)
        encryptedChunks.append(bytearray(encrypt(element)))



    # insert four zero bits for each 7 byte chunk (index bytes excluded)
    # jump over the encrypted repeating chunks including message length temporary for bit shifting operation
    # first read 2x7 bytes with overlap of 1 byte, then insert empty bits to get a valid year date
    # save the resulting data including the zero bits altogether with the index byte as 8 byte chunks into shiftedChunks

    encryptedChunks_iterator = iter(encryptedChunks)
    index = 0
    odd = True
    temp = bytearray(b'')
    #for index, element in enumerate(encryptedChunks_iterator):
    for element in encryptedChunks_iterator:
        #if index == 0 or index % 255 == 0:
        if index == 0:
            element[3] &= int('11111100', 2)    # emtpy bits maskieren
            element[7] &= int('11111100', 2)
            shiftedChunks.append(element)
            index += 1
            continue

        i = element
        chunk1 = i[1:8]
        j = next(encryptedChunks_iterator, bytearray(b''))
        chunk2 = j[1:8]

        # instead of taking repeating bytes with message length, take next element
        if index % 255 == 0:
            if odd:
                temp = j
                temp[3] &= int('11111100', 2)   # emtpy bits maskieren
                temp[7] &= int('11111100', 2)
                j = next(encryptedChunks_iterator, bytearray(b''))
                chunk2 = j[1:8]
                odd = False

            else:
                index = -2
                odd = True
                #temp = next(encryptedChunks_iterator, bytearray(b''))


        # shift chunk2
        if chunk2 != (b''):
            chunk2 = shiftByteArrayLeft(chunk2, 4)
            if len(chunk2) >= 3:
                chunk2 = insertBitGap(chunk2)  # new
        if len(chunk1) >= 3:  # new
            chunk1 = insertBitGap(chunk1)
            if len(chunk1) == 7:  # new
                chunk1[-1] &= int('11111100', 2)  # chunk1 ganz rechts 2 freie Bit maskieren
        if chunk1:  # new
            chunk1.insert(0, i[0])
            shiftedChunks.append(chunk1)
            index += 1

        if temp:
            shiftedChunks.append(temp)
            temp = bytearray(b'')
            index += 1

        if chunk2:  # new
            chunk2.insert(0, j[0])
            shiftedChunks.append(chunk2)
            index += 1




    # padding of the last chunk with zero bytes
    temp = shiftedChunks.pop()
    if len(temp) < 8:
        if len(temp) < 4:
            x = 4 - len(temp)
            temp = b''.join([temp, (0).to_bytes(x, byteorder='big')])
        else:
            lastBytes = temp[4:]
            x = 4 - len(lastBytes)
            lastBytes = b''.join([lastBytes, (0).to_bytes(x, byteorder='big')])
            temp = temp[0:4] + lastBytes

    shiftedChunks.append(bytearray(temp))

    return shiftedChunks




def insertErrorCorrection(inputFile):

    if os.path.isfile(inputFile):
        f = open(inputFile, "rb")
        data = f.read()
        f.close()


        # add redundancy: each 215 bytes we add 40 ecc bytes and get a new chunk size of 255 bytes (~15% redundancy)
        # with this behaviour we share the redundancy over the entire input message and thus over different timestamps
        rs = reedsolo.RSCodec(40)
        #print(data)
        print(len(data))
        dataEncoded = rs.encode(data)
        #print(dataEncoded)
        print(len(dataEncoded))

        return dataEncoded


    else:
        print("No regular file.")
        return 0



def splitDataIntoChunks(inputFile):
    # How many chunks do we need:
    # chunkSize = 8
    chunkSize = 7

    sizeInBytes = os.path.getsize(inputFile)
    # nrOfChunks = math.ceil(sizeInBytes/chunkSize)
    nrOfChunks = sizeInBytes // chunkSize
    if (sizeInBytes % chunkSize != 0):
        nrOfChunks += 1

    print("Size of File:", sizeInBytes, "\nAvailable space per inode:", chunkSize,
          "\nNumber of Chunks:", nrOfChunks)


    chunks = []
    # read file into memory
    if os.path.isfile(inputFile):
        f = open(inputFile, "rb")
        data = f.read()
        f.close()

      
        index = 0
        # split data into multiple chunks
        for i in range(0, sizeInBytes, chunkSize):
            # reset counter when overflow appears (1 Index-Byte yields in max. 0-255 possible values)
            if index == 0 or (index % 256) == 0:
                index = 0
                temp = b"".join([index.to_bytes(1, byteorder='big'), sizeInBytes.to_bytes(7, byteorder='big')])
                # temp = b"".join([index.to_bytes(1, byteorder='big'), nrOfChunks.to_bytes(7, byteorder='big')])

                print("Temp", temp)
                chunks.append(temp)
                index += 1

            print(data[i:i + chunkSize])
            print(index)
            print(index.to_bytes(1, byteorder='big'))
            temp = b"".join([index.to_bytes(1, byteorder='big'), data[i:i + chunkSize]])
            print("Temp", temp)
            chunks.append(temp)
            index += 1
        print(type(chunks))
    else:
        print("No regular file.")

    return chunks



def joinFiles(fileName, noOfChunks, chunkSize):
    dataList = []
    for i in range(0, noOfChunks, 1):
        chunkNum = i * chunkSize
        chunkName = fileName + '%s' % chunkNum
        f = open(chunkName, 'rb')
        dataList.append(f.read())
        f.close()

    f = open(fileName, 'wb')
    for data in dataList:
        f.write(data)
    f.close()


def removeGap(chunk):
    chunk[2] |= ((chunk[3] >> 6) & int('00000011',2))
    chunk[3:] = shiftByteArrayLeft(chunk[3:],2)
    return chunk

def restoreMessage():
    dataList = []
    currentDirectory = os.getcwd()
    print(currentDirectory)
    device = findMountedDevice(currentDirectory)
    print(device)

    blockSize, inodesPerGroup, inodeSize, locationOfInodeTables, locationOfInodeBitmaps, totalInodeCount = getMetadata(
        device)

    shiftedChunks = []
    encryptedChunks = []
    chunksWithIndexByte = []
    chunks = []
    dataEncoded = []

    currentInode = 12
    offsetTimestamp = readTimestamp(device, currentInode, blockSize, inodesPerGroup, inodeSize, locationOfInodeTables)
    decryptedOffsetTimestamp = decrypt(bytes(offsetTimestamp))

    shiftedChunks.append(bytearray(offsetTimestamp))

    numberOfUsedInodes = int.from_bytes(decryptedOffsetTimestamp[1:3], byteorder='big')
    realMessageLength = int.from_bytes(decryptedOffsetTimestamp[4:7], byteorder='big')
    amountOfLastBytes = realMessageLength % 13

    i = currentInode + 1

    # restore multiple timestamps and save into list shiftedChunks
    # amount of timestamps is stored in numberOfUsedInodes
    while i < (currentInode + numberOfUsedInodes):
        timestamp = readTimestamp(device, i, blockSize, inodesPerGroup, inodeSize, locationOfInodeTables)
        shiftedChunks.append(bytearray(timestamp))
        i += 1


    # undo previous shift operations to restore list encryptedChunks (index bytes excluded)
    # jump over the encrypted repeating chunks including message length
    shiftedChunks_iterator = iter(shiftedChunks)
    index = 0
    odd = True
    temp = bytearray(b'')
    counterChunkInserts = 0
    for element in shiftedChunks_iterator:
        #if index == 0 or index % 255 == 0:
        if index == 0:
            encryptedChunks.append(element)
            index += 1
            continue

        # remove gap
        i = element
        chunk1 = i[1:8]
        chunk1 = removeGap(chunk1)

        if len(shiftedChunks) > 1:
            j = next(shiftedChunks_iterator, bytearray(b''))
            chunk2 = j[1:8]

            # jump over repeating bytes with message length
            if index % 255 == 0:
                if odd:
                    temp = j
                    j = next(shiftedChunks_iterator, bytearray(b''))
                    chunk2 = j[1:8]
                    odd = False
                else:
                    index = -2
                    odd = True


            if chunk2 != (b''):
                chunk2 = removeGap(chunk2)
                chunk2 = shiftByteArrayRight(chunk2, 4)

                # concatenate small chunks
                chunk1[6] = (chunk1[6] & int('11110000', 2)) | (chunk2[0] & int('00001111', 2))
                chunk2[0] = (chunk1[6] & int('11110000', 2)) | (chunk2[0] & int('00001111', 2))

            if chunk1:
                chunk1.insert(0, i[0])
                encryptedChunks.append(chunk1)
                counterChunkInserts += 1
                index += 1

            if temp:
                encryptedChunks.append(temp)
                temp = bytearray(b'')
                index += 1

            if chunk2:
                chunk2.insert(0, j[0])
                encryptedChunks.append(chunk2)
                counterChunkInserts += 1
                index += 1


    # remove padding of the last chunk
    if amountOfLastBytes != 0:
        # remove padding on the last chunk
        if amountOfLastBytes >= 7:
            #encryptedChunks.pop()
            amountOfLastBytes -= 6

        lastChunk = encryptedChunks.pop()
        lastChunk = lastChunk[0:1+amountOfLastBytes]
        encryptedChunks.append(lastChunk)



    # add decryption
    for element in encryptedChunks:
        element = bytes(element)
        chunksWithIndexByte.append(bytearray(decrypt(element)))


    # remove index bytes and bytes with message length
    for chunk in chunksWithIndexByte:
        if chunk[0] != 0x00:
            chunks.append(bytearray(chunk[1:8]))


    # remove overlap of 1 byte
    for chunk1,chunk2 in zip(chunks[::2], chunks[1::2]):
        chunk2 = chunk2[1:8]
        dataEncoded.append(chunk1)
        dataEncoded.append(chunk2)
    # bei ungerader Anzahl füge noch letzten chunk hinzu
    if counterChunkInserts % 2 == 1:
        dataEncoded.append(chunks[-1])


    dataDecoded = removeErrorCorrection(dataEncoded)

    if dataDecoded:
        f = open("recovered_message", 'wb')
        f.write(bytes(dataDecoded))
        f.close()

        print("Message Restore succesful.")




def removeErrorCorrection(data):

    completeData = bytes(b'')
    for element in data:
        completeData += bytes(element)

    rs = reedsolo.RSCodec(40)
    dataDecoded = rs.decode(completeData)

    #dataDecoded = completeData

    return dataDecoded




# def readTimestamp(line, blockSize, inodesPerGroup, inodeSize, locationOfInodeTables):
def readTimestamp(device, inodeNumber, blockSize, inodesPerGroup, inodeSize, locationOfInodeTables):

    ddOffsetAccess, ddOffsetCreation = getOffsetForInode(inodeNumber, blockSize, inodesPerGroup, inodeSize,
                                                         locationOfInodeTables)

    with open(device, "rb") as f:
        f.seek(ddOffsetAccess)
        #print(f.tell())
        accessTimestamp = f.read(4)
        f.seek(ddOffsetCreation)
        creationTimestamp = f.read(4)
        accessTimestamp = accessTimestamp[3::-1]
        #print(accessTimestamp)
        creationTimestamp = creationTimestamp[3::-1]
        #print(creationTimestamp)

    return accessTimestamp + creationTimestamp


def getOffsetForInode(inodeNumber, blockSize, inodesPerGroup, inodeSize, locationOfInodeTables):
    groupNumber = (inodeNumber - 1) // inodesPerGroup
    inodeTableIndex = (inodeNumber - 1) % inodesPerGroup
    offsetInodeTable = locationOfInodeTables[groupNumber]
    offsetInodeEntry = inodeTableIndex * inodeSize
    # print(groupNumber, inodeTableIndex, offsetInodeTable, offsetInodeEntry)

    ddOffsetAccess = offsetInodeTable * blockSize + offsetInodeEntry + ACC_TIME_OFFSET
    ddOffsetCreation = offsetInodeTable * blockSize + offsetInodeEntry + CR_TIME_OFFSET

    return ddOffsetAccess, ddOffsetCreation


def getMetadata(device):

    with open(device, "rb") as f:
        # Superblock
        f.seek(1024)  # überspringe bootsektor
        # f.seek(4,1)     #0x4 __le32 s_blocks_count_lo
        totalInodeCount = int.from_bytes(f.read(4), byteorder='little')
        totalBlockCount = int.from_bytes(f.read(4), byteorder='little')
        f.seek(16, 1)  # 0x18 __le32 s_log_block_size
        val = int.from_bytes(f.read(4), byteorder='little')
        blockSize = 1024 * 2 ** val
        f.seek(4, 1)  # 0x20 __le32 s_blocks_per_group
        blocksPerGroup = int.from_bytes(f.read(4), byteorder='little')
        f.seek(4, 1)  # 0x28 __le32 s_inodes_per_group
        inodesPerGroup = int.from_bytes(f.read(4), byteorder='little')
        f.seek(44, 1)  # 0x58 __le16 s_inode_size
        inodeSize = int.from_bytes(f.read(2), byteorder='little')

        # parse length of block group descriptot using the superblock. Calculate number of block groups.
        # Using the primary block group descriptor we are able to calculate the offset of the multiple inode tables

        f.seek(164, 1)  # 0xFE __le16 s_desc_size
        sizeOfGroupDescriptors = int.from_bytes(f.read(2), byteorder='little')

        numberOfBlockGroups = totalBlockCount // blocksPerGroup
        if totalBlockCount % blocksPerGroup != 0:
            numberOfBlockGroups += 1

        # Group Descriptor Table
        f.seek(blockSize)  # jump over first block (bootsektor + superblock)
        f.seek(4, 1)  # 0x4 __le32 bg_inode_bitmap_lo
        locationOfInodeTables = []
        locationOfInodeBitmaps = []
        for i in range(0, numberOfBlockGroups):
            # print(f.tell()) print current position
            locationOfInodeBitmaps.append(int.from_bytes(f.read(4), byteorder='little')) # 0x4 __le32 bg_inode_bitmap_lo
            locationOfInodeTables.append(int.from_bytes(f.read(4), byteorder='little'))  # 0x8 __le32 bg_inode_table_lo
            f.seek(sizeOfGroupDescriptors - 8, 1)

    return blockSize, inodesPerGroup, inodeSize, locationOfInodeTables, locationOfInodeBitmaps, totalInodeCount


def encrypt(chunk):
    # key = hashlib.sha256(b"Passwort")
    # print(key.hexdigest())

    # key = b'testtesttesttest'
    # iv = Random.new().read(AES.block_size)
    # cipher = AES.new(key, AES.MODE_CFB, iv)
    # chiffrat = iv + cipher.encrypt(chuenk)
    # print(chiffrat)

    sender = ARC4.new("Passwort")
    #sender = ARC4.new(bytes(password))
    chiffrat = sender.encrypt(chunk)

    return chiffrat


def decrypt(chunk):

    empfaenger = ARC4.new("Passwort")
    #empfaenger = ARC4.new(password)
    plaintext = empfaenger.decrypt(chunk)

    return plaintext


def findMountedDevice(currentDirectory):
    path = os.path.realpath(os.path.abspath(currentDirectory))
    while not os.path.ismount(path):
        path = os.path.dirname(path)

    with open('/proc/mounts', 'r') as f:
        mounts = [line.split()[0:2] for line in f.readlines()]
        # print(mounts)
        for mount in mounts:
            if mount[1] == path:
                device = mount[0]
    return device


def checkInodeAllocation(inode, device, inodesPerGroup, locationOfInodeBitmaps, blockSize):

    groupNumber = (inode - 1) // inodesPerGroup
    offsetInodeBitmap = locationOfInodeBitmaps[groupNumber]
    # print(offsetInodeBitmap)

    byteWithinInodeBitmap = ((inode - groupNumber * inodesPerGroup) - 1) // 8
    bitWithinInodeBitmap = ((inode - groupNumber * inodesPerGroup) - 1) % 8
    # print(byteWithinInodeBitmap, bitWithinInodeBitmap)

    with open(device, "rb") as f:
        # Inode Bitmap
        f.seek(offsetInodeBitmap * blockSize)  # jump to next respective Inode Bitmap
        f.seek(byteWithinInodeBitmap, 1)  # jump to the respective Byte within Inode Bitmap
        # print(f.tell())
        byteVal = int.from_bytes(f.read(1), byteorder='little')
        # print(byteVal)

    if (byteVal & (1 << bitWithinInodeBitmap)) != 0:
        return True
    else:
        return False


def setTimestamp(device, inodeNumber, chunk, blockSize, inodesPerGroup, inodeSize, locationOfInodeTables):

    ddOffsetAccess, ddOffsetCreation = getOffsetForInode(inodeNumber, blockSize, inodesPerGroup, inodeSize,
                                                         locationOfInodeTables)


    # read 2 Bit for year date
    mask_byteToStore = int('00000011', 2)
    with open("/mnt/masterarbeit/testimage4.dd", 'rb') as f:
        f.seek(ddOffsetAccess)
        byteToStoreAccess = ord(f.read(1))
        f.seek(ddOffsetCreation)
        byteToStoreCreation = ord(f.read(1))

    relevantBitsAccess = byteToStoreAccess & mask_byteToStore
    relevantBitsCreation = byteToStoreCreation & mask_byteToStore

    with open(device, "r+b") as f:
        f.seek(ddOffsetAccess)
        # print(f.tell())
        f.write(chunk[3::-1])
        f.seek(ddOffsetCreation)
        f.write(chunk[7:3:-1])



def hideMessage(inputFile):

    dataEncoded = insertErrorCorrection(inputFile)

    if dataEncoded:
        currentDirectory = os.getcwd()
        print(currentDirectory)
        device = findMountedDevice(currentDirectory)
        print(device)

        blockSize, inodesPerGroup, inodeSize, locationOfInodeTables, locationOfInodeBitmaps, totalInodeCount = getMetadata(
            device)
        print(inodesPerGroup, "\n", locationOfInodeTables, "\n", locationOfInodeBitmaps)
        print(totalInodeCount)

        # print(blockSize, inodesPerGroup, inodeSize, locationOfInodeTables)

        # offset according to password hash
        # pwhash = hashlib.sha256(bytes(input("Enter password: "), "utf-8"))
        # currentInode = pwhash.hexdigest()[25]
        # print(currentInode)


        currentInode = 12
        allocationStatus = checkInodeAllocation(currentInode, device, inodesPerGroup, locationOfInodeBitmaps, blockSize)

        chunks = splitDataIntoChunks13(dataEncoded)

        """
        # add encryption
        encryptedChunks = []
        for chunk in chunks:
            encryptedChunks.append(encrypt(chunk))
        """


        # first check how many allocated inodes are available
        allocatedInodeCount = 0
        for i in range(currentInode, totalInodeCount - currentInode + 1, 1):
            if checkInodeAllocation(i, device, inodesPerGroup, locationOfInodeBitmaps, blockSize):
                allocatedInodeCount += 1

        print("Anzahl allozierte Inodes:", allocatedInodeCount)

        # if there are enough allocated inodes available, then hide data in the next step
        if allocatedInodeCount >= len(chunks):
            for chunk in chunks:
                # Jump over current inode in case it is not allocated.
                while not checkInodeAllocation(currentInode, device, inodesPerGroup, locationOfInodeBitmaps, blockSize):
                    currentInode += 1

                setTimestamp(device, currentInode, chunk, blockSize, inodesPerGroup, inodeSize, locationOfInodeTables)
                currentInode += 1

            print("Message Hiding succesful.")

        else:
            print("Too less allocated inodes. Message to be hidden needs", len(chunks),
                  "allocated inodes, but there are only", allocatedInodeCount, "allocated inodes available.")



def representsInt(s):
    try:
        int(s)
        return True
    except ValueError:
        return False



def createFiles(howManyFiles):
    i = 1
    location = os.getcwd()

    while i <= howManyFiles:
        with open(location + "/" + str(i) + ".txt", 'w') as f:
            #f.write("Testfile:" + str(i) + "\n")
            f.write(str(random.randrange(0, 1000000, 6)))
        # time.sleep( random.uniform( 0,0.25 ) )
        i += 1

    print(str(i - 1), " files created at ", location, " ... \n")


if __name__ == '__main__':
    # readBmpFile()
    # readTimestamp()
    #createFiles(10)

    #fileToHide = "testfile"
    # whereToHide = "/mount_ext/" #default /


    if len(sys.argv) <= 1:
        sys.exit("Please provide the following arguments: If you want to hide or restore the message and in the first case specify a file to hide. Another option creates random files.\n"
                 "Try 'python3 timestamp_magic.py -hide <file to be hidden>' - in case of hiding arbitrary data.\n"
                 "Try 'python3 timestamp_magic.py -restore' - in case of restoring data.\n"
                 "Try 'python3 timestamp_magic.py -createFiles - in case of creating random files.")

    elif len(sys.argv) == 3:
        if sys.argv[1] == "-hide":
            fileToHide = sys.argv[2]
            if os.path.isfile(fileToHide):
                hideMessage(fileToHide)
            else:
                print("Please provide a regular file.")
        elif sys.argv[1] == "-createFiles":
            howManyFiles = sys.argv[2]
            if representsInt(howManyFiles):
                createFiles(int(howManyFiles))
            else:
                print("Please provide a integer instead of string.")
    else:
        if sys.argv[1] == "-restore":
            restoreMessage()
