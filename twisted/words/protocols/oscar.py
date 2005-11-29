# Copyright (c) 2001-2005 Twisted Matrix Laboratories.
# See LICENSE for details.
#
# vim: set sts=4 ts=4 expandtab :

"""An implementation of the OSCAR protocol, which AIM and ICQ use to communcate.

This module is unstable.

Maintainer: U{Daniel Henninger<mailto:jadestorm@nc.rr.com>}
Previous Maintainer: U{Paul Swartz<mailto:z3p@twistedmatrix.com>}
"""

from __future__ import nested_scopes

from twisted.internet import reactor, main, defer, protocol
from twisted.python import log

from scheduler import Scheduler

import struct
import md5
import string
import socket
import random
import time
import types
import re
import binascii
import threading
import socks5, sockserror
import countrycodes

def logPacketData(data):
    # Comment out to display packet log data
    return
    lines = len(data)/16
    if lines*16 != len(data): lines=lines+1
    for i in range(lines):
        d = tuple(data[16*i:16*i+16])
        hex = map(lambda x: "%02X"%ord(x),d)
        text = map(lambda x: (len(repr(x))>3 and '.') or x, d)
        log.msg(' '.join(hex)+ ' '*3*(16-len(d)) +''.join(text))
    log.msg('')

def bitstostr(num, size):
    bitstring = ''
    if num < 0: return
    if num == 0: return '0'*size
    cnt = 0
    while cnt < size:
        bitstring = str(num % 2) + bitstring
        num = num >> 1
        cnt = cnt + 1
    return bitstring

def SNAC(fam,sub,id,data,flags=[0,0]):
    head=struct.pack("!HHBBL",fam,sub,
                     flags[0],flags[1],
                     id)
    return head+str(data)

def readSNAC(data):
    if len(data) < 10: return None
    head=list(struct.unpack("!HHBBL",data[:10]))
    datapos = 10
    if 0x80 & head[2]:
        # Ah flag 0x8000, this is some sort of family indicator, skip it,
        # we don't care.
        sLen,id,length = struct.unpack(">HHH", data[datapos:datapos+6])
        datapos = datapos + 6 + length
    return head+[data[datapos:]]

def TLV(type,value):
    head=struct.pack("!HH",type,len(value))
    return head+str(value)

def readTLVs(data,count=None):
    dict={}
    while data and len(dict)!=count:
        head=struct.unpack("!HH",data[:4])
        dict[head[0]]=data[4:4+head[1]]
        data=data[4+head[1]:]
    if not count:
        return dict
    return dict,data

def encryptPasswordMD5(password,key):
    m=md5.new()
    m.update(key)
    m.update(md5.new(password).digest())
    m.update("AOL Instant Messenger (SM)")
    return m.digest()

def encryptPasswordICQ(password):
    key=[0xF3,0x26,0x81,0xC4,0x39,0x86,0xDB,0x92,0x71,0xA3,0xB9,0xE6,0x53,0x7A,0x95,0x7C]
    bytes=map(ord,password)
    r=""
    for i in range(len(bytes)):
        r=r+chr(bytes[i]^key[i%len(key)])
    return r

def dehtml(text):
    if (not text):
        text = ""
    text=re.sub('<[Bb][Rr]>',"\n",text)
    text=re.sub('<[^>]*>','',text)
    text=string.replace(text,'&gt;','>')
    text=string.replace(text,'&lt;','<')
    text=string.replace(text,'&nbsp;',' ')
    text=string.replace(text,'&amp;','&')
    text=string.replace(text,'&quot;',"'")
    return text

def html(text):
    if (not text):
        text = ""
    text=string.replace(text,'&','&amp;')
    text=string.replace(text,'<','&lt;')
    text=string.replace(text,'>','&gt;')
    text=string.replace(text,"\n","<br>")
    return '<html><body bgcolor="white"><font color="black">%s</font></body></html>'%text


class OSCARUser:
    def __init__(self, name, warn, tlvs):
        self.name = name
        self.warning = warn
        self.flags = []
        self.caps = []
        self.icqIPaddy = None
        self.icqLANIPaddy = None
        self.icqLANIPport = None
        self.icqProtocolVersion = None
        self.status = ""
        self.idleTime = 0
        self.iconhash = None
        self.iconflags = None
        for k,v in tlvs.items():
            if k == 0x0001: # user flags
                v=struct.unpack('!H',v)[0]
                for o, f in [(0x0001,'unconfirmed'),
                             (0x0002,'admin'),
                             (0x0004,'staff'),
                             (0x0008,'commercial'),
                             (0x0010,'free'),
                             (0x0020,'away'),
                             (0x0040,'icq'),
                             (0x0080,'wireless'),
                             (0x0100,'unknown'),
                             (0x0200,'unknown'),
                             (0x0400,'active'),
                             (0x0800,'unknown'),
                             (0x1000,'abinternal')]:
                    if v&o: self.flags.append(f)
            elif k == 0x0002: # account creation time
                self.createdOn = struct.unpack('!L',v)[0]
            elif k == 0x0003: # on-since
                self.onSince = struct.unpack('!L',v)[0]
            elif k == 0x0004: # idle time
                self.idleTime = struct.unpack('!H',v)[0]
            elif k == 0x0005: # member since
                self.memberSince = struct.unpack('!L',v)[0]
            elif k == 0x0006: # icq online status
                if   v[0:2] == '\x00\x00\x00':
                    self.icqStatus = 'online'
                elif v[0:2] == '\x00\x00\x01':
                    self.icqStatus = 'away'
                elif v[0:2] == '\x00\x00\x02':
                    self.icqStatus = 'dnd'
                elif v[0:2] == '\x00\x00\x04':
                    self.icqStatus = 'xa'
                elif v[0:2] == '\x00\x00\x10':
                    self.icqStatus = 'busy'
                elif v[0:2] == '\x00\x00\x20':
                    self.icqStatus = 'chat'
                elif v[0:2] == '\x00\x01\x00':
                    self.icqStatus = 'invisible'
                elif v[0:2] == '\x01\x00\x00':
                    self.icqStatus = 'webaware'
                elif v[0:2] == '\x02\x00\x00':
                    self.icqStatus = 'hideip'
                elif v[0:2] == '\x08\x00\x00':
                    self.icqStatus = 'birthday'
                else:
                    self.icqStatus = 'unknown'
            elif k == 0x0008: # client type?
                pass
            elif k == 0x000a: # icq user ip address
                self.icqIPaddy = socket.inet_ntoa(v)
            elif k == 0x000c: # icq random stuff
                # from http://iserverd1.khstu.ru/oscar/info_block.html
                self.icqRandom = struct.unpack('!4sLBHLLLLLLH',v)
                self.icqLANIPaddy = socket.inet_ntoa(self.icqRandom[0])
                self.icqLANIPport = self.icqRandom[1]
                self.icqProtocolVersion = self.icqRandom[3]
            elif k == 0x000d: # capabilities
                caps=[]
                while v:
                    c=v[:16]

                    if CAPS.has_key(c): caps.append(CAPS[c])
                    else: caps.append(("unknown",c))
                    v=v[16:]
                caps.sort()
                self.caps=caps
            elif k == 0x000e: # AOL capability information
                pass
            elif k == 0x000f: # session length (aim)
                self.sessionLength = struct.unpack('!L',v)[0]
            elif k == 0x0010: # session length (aol)
                self.sessionLength = struct.unpack('!L',v)[0]
            elif k == 0x0019: # OSCAR short capabilities
                pass
            elif k == 0x001a: # AOL short capabilities
                pass
            elif k == 0x001b: # encryption certification MD5 checksum
                pass
            elif k == 0x001d: # AIM Extended Status
                log.msg("AIM Extended Status: user %s\nv: %s"%(self.name,repr(v)))
                while len(v)>4 and ord(v[0]) == 0 and ord(v[3]) != 0:
                    exttype,extflags,extlen = struct.unpack('!HBB',v[0:4])
                    if exttype == 0x00: # Gaim skips this, so will we
                        pass
                    elif exttype == 0x01: # Actual interesting buddy icon
                        if extlen > 0 and (extflags == 0x00 or extflags == 0x01):
                            self.iconhash = v[4:4+extlen]
                            self.icontype = extflags
                            log.msg("   extracted icon hash: extflags = %s, iconhash = %s" % (str(hex(extflags)), binascii.hexlify(self.iconhash)))
                    elif exttype == 0x02: # Extended Status Message
                        if extlen >= 4: # Why?  Gaim does this
                            availlen = (struct.unpack('!H', v[4:6]))[0]
                            self.status = v[6:6+availlen]
                            pos = 6+availlen
                            hasencoding = (struct.unpack('!H',v[pos:pos+2]))[0]
                            pos = pos+2
                            self.statusencoding = None
                            if hasencoding == 0x0001:
                                enclen = (struct.unpack('!HH',v[pos:pos+4]))[1]
                                self.statusencoding = v[pos+4:pos+4+enclen]
                            log.msg("   extracted status message: %s"%(self.status))
                            if self.statusencoding:
                                log.msg("   status message encoding: %s"%(str(self.statusencoding)))
                    else:
                        log.msg("   unknown extended status type: %d\ndata: %s"%(ord(v[1]), repr(v[:ord(v[3])+4])))
                    v=v[ord(v[3])+4:]
            elif k == 0x001e: # unknown
                pass
            elif k == 0x001f: # unknown
                pass
            else:
                log.msg("unknown tlv for user %s\nt: %s\nv: %s"%(self.name,str(hex(k)),repr(v)))

    def __str__(self):
        s = '<OSCARUser %s' % self.name
        o = []
        if self.warning!=0: o.append('warning level %s'%self.warning)
        if hasattr(self, 'flags'): o.append('flags %s'%self.flags)
        if hasattr(self, 'sessionLength'): o.append('online for %i minutes' % (self.sessionLength/60,))
        if hasattr(self, 'idleTime'): o.append('idle for %i minutes' % self.idleTime)
        if self.caps: o.append('caps %s'%self.caps)
        if o:
            s=s+', '+', '.join(o)
        s=s+'>'
        return s


class SSIGroup:
    def __init__(self, name, groupID, buddyID, tlvs = {}):
        self.name = name
        self.groupID = groupID
        self.buddyID = buddyID
        #self.tlvs = []
        #self.userIDs = []
        self.usersToID = {}
        self.users = []
        #if not tlvs.has_key(0xC8): return
        #buddyIDs = tlvs[0xC8]
        #while buddyIDs:
        #    bid = struct.unpack('!H',buddyIDs[:2])[0]
        #    buddyIDs = buddyIDs[2:]
        #    self.users.append(bid)

    def findIDFor(self, user):
        return self.usersToID[user]

    def addUser(self, buddyID, user):
        self.usersToID[user] = buddyID
        self.users.append(user)
        user.group = self

    def delUser(self, user):
        buddyID = self.usersToID[user]
        self.users.remove(user)
        del self.usersToID[user]
        user.group = None

    def oscarRep(self):
        data = struct.pack(">H", len(self.name)) +self.name
        tlvs = TLV(0xc8, struct.pack(">H",len(self.users)))
        data += struct.pack(">4H", self.groupID, self.buddyID, 1, len(tlvs))
        return data+tlvs
#      if len(self.users) > 0:
#              tlvData = TLV(0xc8, reduce(lambda x,y:x+y, [struct.pack('!H',self.usersToID[x]) for x in self.users]))
#      else:
#              tlvData = ""
#        return struct.pack('!H', len(self.name)) + self.name + \
#               struct.pack('!HH', groupID, buddyID) + '\000\001' + \
#               struct.pack(">H", len(tlvData)) + tlvData

    def __str__(self):
        s = '<SSIGroup %s (ID %d)' % (self.name, self.buddyID)
        if len(self.users) > 0:
            s=s+' (Members:'+', '.join(self.users)+')'
        s=s+'>'
        return s


class SSIBuddy:
    def __init__(self, name, groupID, buddyID, tlvs = {}):
        self.name = name
        self.nick = name
        self.groupID = groupID
        self.buddyID = buddyID
        self.tlvs = tlvs
        self.authorizationRequestSent = False
        self.authorized = True
        for k,v in tlvs.items():
            if k == 0x0066: # awaiting authorization
                self.authorized = False
            elif k == 0x0131: # buddy nick
                self.nick = v
            elif k == 0x013c: # buddy comment
                self.buddyComment = v
            elif k == 0x013d: # buddy alerts
                actionFlag = ord(v[0])
                whenFlag = ord(v[1])
                self.alertActions = []
                self.alertWhen = []
                if actionFlag&1:
                    self.alertActions.append('popup')
                if actionFlag&2:
                    self.alertActions.append('sound')
                if whenFlag&1:
                    self.alertWhen.append('online')
                if whenFlag&2:
                    self.alertWhen.append('unidle')
                if whenFlag&4:
                    self.alertWhen.append('unaway')
            elif k == 0x013e:
                self.alertSound = v
 
    def oscarRep(self):
        data = struct.pack(">H", len(self.name)) + self.name
        tlvs = ""
        if not self.authorized:
            tlvs += TLV(0x0066, "") # awaiting authorization
        data += struct.pack(">4H", self.groupID, self.buddyID, 0, len(tlvs))
        return data+tlvs
#        tlvData = reduce(lambda x,y: x+y, map(lambda (k,v):TLV(k,v), self.tlvs.items()), '\000\000')
#        return struct.pack('!H', len(self.name)) + self.name + \
#               struct.pack('!HH', groupID, buddyID) + '\000\000' + tlvData

    def __str__(self):
        s = '<SSIBuddy %s (ID %d)' % (self.name, self.buddyID)
        s=s+'>'
        return s


class SSIIconSum:
    def __init__(self, name="1", groupID=0x0000, buddyID=0x51f4, tlvs = {}):
        self.name = name
        self.buddyID = buddyID
        self.groupID = groupID
        self.iconSum = tlvs.get(0xd5,"")

    def updateIcon(self, iconData):
        m=md5.new()
        m.update(iconData)
        self.iconSum = m.digest()
        log.msg("icon sum is %s" % binascii.hexlify(self.iconSum))
 
    def oscarRep(self):
        data = struct.pack(">H", len(self.name)) + self.name
        tlvs = TLV(0x00d5,struct.pack('!BB', 0x00, len(self.iconSum))+self.iconSum)+TLV(0x0131, "")
        data += struct.pack(">4H", self.groupID, self.buddyID, 0x0014, len(tlvs))
        return data+tlvs

    def __str__(self):
        s = '<SSIIconSum %s:%s (ID %d)' % (self.name, binascii.hexlify(self.iconSum), self.buddyID)
        s=s+'>'
        return s


class OscarConnection(protocol.Protocol):
    def connectionMade(self):
        self.state=""
        self.seqnum=0
        self.buf=''
        self.outRate=6000
        self.outTime=time.time()
        self.stopKeepAliveID = None
        self.setKeepAlive(240) # 240 seconds = 4 minutes

    def connectionLost(self, reason):
        log.msg("Connection Lost! %s" % self)
        self.stopKeepAlive()
        self.transport.loseConnection()

    def connectionFailed(self):
        log.msg("Connection Failed! %s" % self)
        self.stopKeepAlive()

    def sendFLAP(self,data,channel = 0x02):
        if not hasattr(self, "seqnum"):
             self.seqnum = 0
        self.seqnum=(self.seqnum+1)%0xFFFF
        seqnum=self.seqnum
        head=struct.pack("!BBHH", 0x2a, channel,
                         seqnum, len(data))
        self.transport.write(head+str(data))
        #if isinstance(self, ChatService):
        #    logPacketData(head+str(data))

    def readFlap(self):
        if len(self.buf)<6: return # We don't have a whole FLAP yet
        flap=struct.unpack("!BBHH",self.buf[:6])
        if len(self.buf)<6+flap[3]: return # We don't have a whole FLAP yet
        if flap[0] != 0x2a:
            log.msg("WHOA! Illegal FLAP id!  %x" % flap[0])
            return
        data,self.buf=self.buf[6:6+flap[3]],self.buf[6+flap[3]:]
        return [flap[1],data]

    def dataReceived(self,data):
        logPacketData(data)
        self.buf=self.buf+data
        flap=self.readFlap()
        while flap:
            if flap[0] == 0x04:
                # We failed to connect properly
                self.connectionLost("Connection rejected.")
            func=getattr(self,"oscar_%s"%self.state,None)
            if not func:
                log.msg("no func for state: %s" % self.state)
            state=func(flap)
            if state:
                self.state=state
            flap=self.readFlap()

    def setKeepAlive(self,t):
        self.keepAliveDelay=t
        if hasattr(self,"stopKeepAliveID") and self.stopKeepAliveID:
            self.stopKeepAlive()
        self.stopKeepAliveID = reactor.callLater(t, self.sendKeepAlive)

    def sendKeepAlive(self):
        self.sendFLAP("",0x05)
        self.stopKeepAliveID = reactor.callLater(self.keepAliveDelay, self.sendKeepAlive)

    def stopKeepAlive(self):
        if hasattr(self,"stopKeepAliveID") and self.stopKeepAliveID:
            self.stopKeepAliveID.cancel()
            self.stopKeepAliveID = None

    def disconnect(self):
        """
        send the disconnect flap, and sever the connection
        """
        self.sendFLAP('', 0x04)
        def f(reason): pass
        self.connectionLost = f
        self.transport.loseConnection()


class SNACBased(OscarConnection):
    snacFamilies = {
        # family : (version, toolID, toolVersion)
    }
    def __init__(self,cookie):
        self.cookie=cookie
        self.lastID=0
        self.supportedFamilies = {}
        self.requestCallbacks={} # request id:Deferred
        self.scheduler=Scheduler(self.sendFLAP)

    def sendSNAC(self,fam,sub,data,flags=[0,0]):
        """
        send a snac and wait for the response by returning a Deferred.
        """
        if not self.supportedFamilies.has_key(fam):
            log.msg("Ignoring attempt to send unsupported SNAC family %s." % (str(hex(fam))))
            return defer.fail("Attempted to send unsupported SNAC family.")

        reqid=self.lastID
        self.lastID=reqid+1
        d = defer.Deferred()
        d.reqid = reqid

        d.addErrback(self._ebDeferredError,fam,sub,data) # XXX for testing

        self.requestCallbacks[reqid] = d
        snac=SNAC(fam,sub,reqid,data)
        self.scheduler.enqueue(fam,sub,snac)
        return d

    def _ebDeferredError(self, error, fam, sub, data):
        log.msg('ERROR IN DEFERRED %s' % error)
        log.msg('on sending of message, family 0x%02x, subtype 0x%02x' % (fam, sub))
        log.msg('data: %s' % repr(data))

    def sendSNACnr(self,fam,sub,data,flags=[0,0]):
        """
        send a snac, but don't bother adding a deferred, we don't care.
        """
        if not self.supportedFamilies.has_key(fam):
            log.msg("Ignoring attempt to send unsupported SNAC family %s." % (str(hex(fam))))
            return

        snac=SNAC(fam,sub,0x10000*fam+sub,data)
        self.scheduler.enqueue(fam,sub,snac)

    def oscar_(self,data):
        self.sendFLAP("\000\000\000\001"+TLV(6,self.cookie), 0x01)
        return "Data"

    def oscar_Data(self,data):
        snac=readSNAC(data[1])
        if not snac:
            log.msg("Illegal SNAC data received in oscar_Data: %s" % data)
            return
        if self.requestCallbacks.has_key(snac[4]):
            d = self.requestCallbacks[snac[4]]
            del self.requestCallbacks[snac[4]]
            if snac[1]!=1:
                d.callback(snac)
            else:
                d.errback(snac)
            return
        func=getattr(self,'oscar_%02X_%02X'%(snac[0],snac[1]),None)
        if not func:
            self.oscar_unknown(snac)
        else:
            func(snac[2:])
        return "Data"

    def oscar_unknown(self,snac):
        log.msg("unknown for %s" % self)
        log.msg(snac)


    def oscar_01_03(self, snac):
        numFamilies = len(snac[3])/2
        serverFamilies = struct.unpack("!"+str(numFamilies)+'H', snac[3])
        d = ''
        for fam in serverFamilies:
            log.msg("Server supports SNAC family %s" % (str(hex(fam))))
            self.supportedFamilies[fam] = True
            if self.snacFamilies.has_key(fam):
                d=d+struct.pack('!2H',fam,self.snacFamilies[fam][0])
        self.sendSNACnr(0x01,0x17, d)

    def oscar_01_0A(self,snac):
        """
        change of rate information.
        """
        # this can be parsed, maybe we can even work it in
        info=struct.unpack('!HHLLLLLLL',snac[3][8:40])
        code=info[0]
        rateclass=info[1]
        window=info[2]
        clear=info[3]
        alert=info[4]
        limit=info[5]
        disconnect=info[6]
        current=info[7]
        maxrate=info[8]
      
        self.scheduler.setStat(rateclass,window=window,clear=clear,alert=alert,limit=limit,disconnect=disconnect,rate=current,maxrate=maxrate)

        #need to figure out a better way to do this
        #if (code==3):
        #    import sys
        #    sys.exit()

    def oscar_01_18(self,snac):
        """
        host versions, in the same format as we sent
        """
        self.sendSNACnr(0x01,0x06,"") #pass

    def clientReady(self):
        """
        called when the client is ready to be online
        """
        d = ''
        for fam in self.supportedFamilies:
            log.msg("Checking for client SNAC family support %s" % str(hex(fam)))
            if self.snacFamilies.has_key(fam):
                version, toolID, toolVersion = self.snacFamilies[fam]
                log.msg("    We do support at %s %s %s" % (str(version), str(hex(toolID)), str(hex(toolVersion))))
                d = d + struct.pack('!4H',fam,version,toolID,toolVersion)
        self.sendSNACnr(0x01,0x02,d)


class BOSConnection(SNACBased):
    snacFamilies = {
        0x01:(3, 0x0110, 0x0629),
        0x02:(1, 0x0110, 0x0629),
        0x03:(1, 0x0110, 0x0629),
        0x04:(1, 0x0110, 0x0629),
        0x06:(1, 0x0110, 0x0629),
        0x08:(1, 0x0104, 0x0001),
        0x09:(1, 0x0110, 0x0629),
        0x0a:(1, 0x0110, 0x0629),
        0x0b:(1, 0x0104, 0x0001),
        0x0c:(1, 0x0104, 0x0001),
        0x13:(3, 0x0110, 0x0629),
        0x15:(1, 0x0110, 0x047c)
    }

    capabilities = None
    statusindicators = 0x0000

    def __init__(self,username,cookie):
        SNACBased.__init__(self,cookie)
        self.username=username
        self.profile = None
        self.awayMessage = None
        self.services = {}
        self.socksProxyServer = None
        self.socksProxyPort = None

        if not self.capabilities:
            self.capabilities = [CAP_CHAT]

    def parseUser(self,data,count=None):
        l=ord(data[0])
        name=data[1:1+l]
        warn,foo=struct.unpack("!HH",data[1+l:5+l])
        warn=int(warn/10)
        tlvs=data[5+l:]
        if count:
            tlvs,rest = readTLVs(tlvs,foo)
        else:
            tlvs,rest = readTLVs(tlvs), None
        u = OSCARUser(name, warn, tlvs)
        if rest == None:
            return u
        else:
            return u, rest

    def parseMoreInfo(self, data):
        # why did i have this here and why did dsh remove it
        #result = ord(data[0])
        #if result != 0xa:
        #    return

        pos = 3
        homepagelen = struct.unpack("<H", data[pos:pos+2])[0]
        pos += 2
        homepage = data[pos:pos+homepagelen-1]

        pos += homepagelen
        year  = struct.unpack("<H", data[pos:pos+2])[0]
        month = struct.unpack("B", data[pos+2:pos+3])[0]
        day   = struct.unpack("B", data[pos+3:pos+4])[0]
        if year and month and day:
            birth = "%04d-%02d-%02d"%(year,month,day)
        else:
            birth = ""
 
        return homepage,birth

    def parseWorkInfo(self, data):
        #result = ord(data[0])
        #if result != 0xa:
        #    return

        pos = 0
        citylen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        city = data[pos:pos+citylen-1]

        pos += citylen
        statelen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        state = data[pos:pos+statelen-1]

        pos += statelen
        phonelen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        phone = data[pos:pos+phonelen-1]

        pos += phonelen
        faxlen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        fax = data[pos:pos+faxlen-1]

        pos += faxlen
        addresslen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        address = data[pos:pos+addresslen-1]

        pos += addresslen
        ziplen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        zip = data[pos:pos+ziplen-1]

        pos += ziplen
        countrycode = struct.unpack(">H",data[pos:pos+2])[0]
        if countrycode in countrycodes.countryCodes:
            country = countrycodes.countryCodes[countrycode]
        else:
            country = ""

        pos += 2
        companylen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        company = data[pos:pos+companylen-1]

        pos += companylen
        departmentlen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        department = data[pos:pos+departmentlen-1]

        pos += departmentlen
        positionlen = struct.unpack("<H",data[pos:pos+2])[0]
        pos += 2
        position = data[pos:pos+positionlen-1]

        return city,state,phone,fax,address,zip,country,company,department,position

    def parseNotesInfo(self, data):
        #result = ord(data[0])
        #if result != 0xa:
        #    return

        noteslen = struct.unpack("<H", data[0:2])[0]
        notes = data[2:2+noteslen-1]
        return notes

    def parseFullInfo(self, data):
        #result = ord(data[0])
        #if result != 0xa:
        #    return
        pos = 0
        nicklen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        nick = data[pos:pos + nicklen - 1]

        pos += nicklen
        firstlen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        first = data[pos:pos + firstlen - 1]

        pos += firstlen
        lastlen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        last = data[pos:pos + lastlen - 1]

        pos += lastlen
        emaillen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        email = data[pos:pos + emaillen - 1]

        pos += emaillen
        homeCitylen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        homeCity = data[pos:pos + homeCitylen - 1]

        pos += homeCitylen
        homeStatelen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        homeState = data[pos:pos + homeStatelen - 1]

        pos += homeStatelen
        homePhonelen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        homePhone = data[pos:pos + homePhonelen - 1]

        pos += homePhonelen
        homeFaxlen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        homeFax = data[pos:pos + homeFaxlen - 1]

        pos += homeFaxlen
        homeAddresslen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        homeAddress = data[pos:pos + homeAddresslen - 1]

        pos += homeAddresslen
        cellPhonelen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        cellPhone = data[pos:pos + cellPhonelen - 1]

        pos += cellPhonelen
        homeZiplen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        homeZip = data[pos:pos + homeZiplen - 1]

        pos += homeZiplen
        homeCountrycode = struct.unpack("<H", data[pos:pos+2])[0]

        if homeCountrycode in countrycodes.countryCodes:
            homeCountry = countrycodes.countryCodes[homeCountrycode]
        else:
            homeCountry = ""

        return nick,first,last,email,homeCity,homeState,homePhone,homeFax,homeAddress,cellPhone,homeZip,homeCountry

    def parseBasicInfo(self,data):
        #result = ord(data[0])

        pos = 0
        nicklen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        nick = data[pos:pos + nicklen - 1]

        pos += nicklen
        firstlen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        first = data[pos:pos + firstlen - 1]

        pos += firstlen
        lastlen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        last = data[pos:pos + lastlen - 1]

        pos += lastlen
        emaillen = struct.unpack('<H', data[pos:pos+2])[0]
        pos += 2
        email = data[pos:pos + emaillen - 1]

        return nick,first,last,email

    def oscar_01_05(self, snac, d = None):
        """
        data for a new service connection
        d might be a deferred to be called back when the service is ready
        """
        tlvs = readTLVs(snac[3][0:])
        service = struct.unpack('!H',tlvs[0x0d])[0]
        ip = tlvs[5]
        cookie = tlvs[6]

        def addService(x):
            self.services[service] = x

        #c = serviceClasses[service](self, cookie, d)
        if self.socksProxyServer and self.socksProxyPort:
            c = protocol.ProxyClientCreator(reactor, serviceClasses[service], self, cookie, d)
            c.connectSocks5Proxy(ip, 5190, self.socksProxyServer, int(self.socksProxyPort), "BOSCONN").addCallback(addService)
        else:
            c = protocol.ClientCreator(reactor, serviceClasses[service], self, cookie, d)
            c.connectTCP(ip, 5190).addCallback(addService)
        #self.services[service] = c

    def oscar_01_07(self,snac):
        """
        rate paramaters
        """
        self.outRateInfo={}
        self.outRateTable={}
        count=struct.unpack('!H',snac[3][0:2])[0]
        snac[3]=snac[3][2:]
        for i in range(count):
            info=struct.unpack('!HLLLLLLL',snac[3][:30])
            classid=info[0]
            window=info[1]
            clear=info[2]
            currentrate=info[6]
            lasttime=time.time()
            maxrate=info[7]
            self.scheduler.setStat(classid,window=window,clear=clear,rate=currentrate,lasttime=lasttime,maxrate=maxrate)
            snac[3]=snac[3][35:]

        while (len(snac[3]) > 0):
            info=struct.unpack('!HH',snac[3][:4])
            classid=info[0]
            count=info[1]
            info=struct.unpack('!'+str(2*count)+'H',snac[3][4:4+count*4])
            while (len(info)>0):
                fam,sub=str(info[0]),str(info[1])
                self.scheduler.bindIntoClass(fam,sub,classid)
                info=info[2:]
            snac[3]=snac[3][4+count*4:]             

        self.sendSNACnr(0x01,0x08,"\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05") # ack
        self.initDone()
        self.sendSNACnr(0x13,0x02,'') # SSI rights info
        self.sendSNACnr(0x02,0x02,'') # location rights info
        self.sendSNACnr(0x03,0x02,'') # buddy list rights
        self.sendSNACnr(0x04,0x04,'') # ICBM parms
        self.sendSNACnr(0x09,0x02,'') # BOS rights

    def oscar_01_0F(self,snac):
        """
        Receive Self User Info
        """
        log.msg('Received Self User Info %s' % str(snac))
        self.receivedSelfInfo(self.parseUser(snac[3]))

    def oscar_01_10(self,snac):
        """
        we've been warned
        """
        skip = struct.unpack('!H',snac[3][:2])[0]
        newLevel = struct.unpack('!H',snac[3][2+skip:4+skip])[0]/10
        if len(snac[3])>4+skip:
            by = self.parseUser(snac[3][4+skip:])
        else:
            by = None
        self.receiveWarning(newLevel, by)

    def oscar_01_13(self,snac):
        """
        MOTD
        """
        motd_msg_type = struct.unpack('!H', snac[3][:2])[0]
        if MOTDS.has_key(motd_msg_type):
            tlvs = readTLVs(snac[3][2:])
            motd_msg_string = tlvs[0x0b]

    def oscar_01_21(self,snac):
        """
        Receive extended status info
        """
        v = snac[3]
        log.msg('Received extended status info for %s: %s' % (self.username, str(snac)))

        while len(v)>4 and ord(v[0]) == 0 and ord(v[3]) != 0:
            exttype = (struct.unpack('!H',v[0:2]))[0]
            if exttype == 0x00 or exttype == 0x01: # Why are there two?
                iconflags, iconhashlen = struct.unpack('!BB',v[2:4])
                iconhash = v[4:4+iconhashlen]
                log.msg("   extracted icon hash: flags = %s, flags-as-hex = %s, iconhash = %s" % (bitstostr(iconflags, 8), str(hex(iconflags)), binascii.hexlify(iconhash)))
                if iconflags == 0x41:
                    self.requestBuddyIcon(iconhash)
            elif exttype == 0x02: # Extended Status Message
                # I'm not sure if we should do something about this here?
                statlen=int((struct.unpack('!H', v[2:4]))[0])
                status=v[4:4+statlen]
                log.msg("   extracted status message: %s"%(status))
            else:
                log.msg("   unknown extended status type: %d\ndata: %s"%(ord(v[1]), repr(v[:ord(v[3])+4])))
            v=v[ord(v[3])+4:]

    def oscar_02_03(self, snac):
        """
        location rights response
        """
        tlvs = readTLVs(snac[3])
        self.maxProfileLength = tlvs[1]

    def oscar_03_03(self, snac):
        """
        buddy list rights response
        """
        tlvs = readTLVs(snac[3])
        self.maxBuddies = tlvs[1]
        self.maxWatchers = tlvs[2]

    def oscar_03_0B(self, snac):
        """
        buddy update
        """
        self.updateBuddy(self.parseUser(snac[3]))

    def oscar_03_0C(self, snac):
        """
        buddy offline
        """
        self.offlineBuddy(self.parseUser(snac[3]))

#    def oscar_04_03(self, snac):

    def oscar_04_05(self, snac):
        """
        ICBM parms response
        """
        self.sendSNACnr(0x04,0x02,'\x00\x00\x00\x00\x00\x0b\x1f@\x03\xe7\x03\xe7\x00\x00\x00\x00') # IM rights

    def oscar_04_07(self, snac):
        """
        ICBM message (instant message)
        """
        data = snac[3]
        cookie, data = data[:8], data[8:]
        channel = struct.unpack('!H',data[:2])[0]
        data = data[2:]
        user, data = self.parseUser(data, 1)
        tlvs = readTLVs(data)
        if channel == 1: # message
            flags = []
            multiparts = []
            for k, v in tlvs.items():
                if k == 0x02: # message data
                    log.msg("Message data: %s" % (repr(v)))
                    while v:
                        #2005/09/25 13:55 EDT [B,client] Message data: '\x05\x01\x00\x01\x01\x01\x01\x00\xaf\x00\x03\x00\x00<html><body ichatballooncolor="#7BB5EE" ichattextcolor="#000000"><font face="Courier" ABSZ=12 color="#000000">test\xe4ng the transport for fun and profit</font></body></html>'
                        fragtype,fragver,fraglen = struct.unpack('!BBH', v[:4])
                        if fragtype == 0x05:
                            # This is a required capabilities list
                            # We really have no idea what to do with this...
                            # actual capabilities seen have been 0x01... text?
                            # we shall move on with our lives
                            pass
                        elif fragtype == 0x01:
                            # This is what we're realllly after.. message data.
                            charSet, charSubSet = struct.unpack('!HH', v[4:8])
                            messageLength = fraglen - 4 # ditch the charsets
                            message = [v[8:8+messageLength]]

                            if charSet == 0x0000:
                                message.append('ascii')
                            elif charSet == 0x0002:
                                message.append('unicode')
                            elif charSet == 0x0003:
                                message.append('custom') # iso-8859-1?
                            elif charSet == 0xffff:
                                message.append('none')
                            else:
                                message.append('unknown')

                            if charSubSet == 0x0000:
                                message.append('standard')
                            elif charSubSet == 0x000b:
                                message.append('macintosh')
                            elif charSubSet == 0xffff:
                                message.append('none')
                            else:
                                message.append('unknown')

                            if messageLength > 0: multiparts.append(tuple(message))
                        else:
                            # Uh... what is this???
                            log.msg("unknown message fragment %d %d: %v" % (fragtype, fragver, str(v)))
                        v = v[4+fraglen:]
                elif k == 0x03: # server ack requested
                    flags.append('acknowledge')
                elif k == 0x04: # message is auto response
                    flags.append('auto')
                elif k == 0x06: # message received offline
                    flags.append('offline')
                elif k == 0x08: # has a buddy icon
                    iconLength, foo, iconSum, iconStamp = struct.unpack('!LHHL',v)
                    if iconLength:
                        flags.append('icon')
                        flags.append((iconLength, iconSum, iconStamp))
                elif k == 0x09: # request for buddy icon
                    flags.append('buddyrequest')
                elif k == 0x0b: # non-direct connect typing notification
                    flags.append('typingnot')
                elif k == 0x17: # extra data.. wonder what this is?
                    flags.append('extradata')
                    flags.append(v)
                else:
                    log.msg('unknown TLV for incoming IM, %04x, %s' % (k,repr(v)))

#  unknown tlv for user SNewdorf
#  t: 29
#  v: '\x00\x00\x00\x05\x02\x01\xd2\x04r\x00\x01\x01\x10/\x8c\x8b\x8a\x1e\x94*\xbc\x80}\x8d\xc4;\x1dEM'
# XXX what is this?
            self.receiveMessage(user, multiparts, flags)
        elif channel == 2: # rendezvous
            status = struct.unpack('!H',tlvs[5][:2])[0]
            requestClass = tlvs[5][10:26]
            moreTLVs = readTLVs(tlvs[5][26:])
            if requestClass == CAP_CHAT: # a chat request
                exchange = None
                name = None
                instance = None
                if moreTLVs.has_key(10001):
                    exchange = struct.unpack('!H',moreTLVs[10001][:2])[0]
                    name = moreTLVs[10001][3:-2]
                    instance = struct.unpack('!H',moreTLVs[10001][-2:])[0]
                if not exchange or not name or not instance:
                    self.chatInvitationAccepted(user)
                    return
                if not self.services.has_key(SERVICE_CHATNAV):
                    self.connectService(SERVICE_CHATNAV,1).addCallback(lambda x: self.services[SERVICE_CHATNAV].getChatInfo(exchange, name, instance).\
                        addCallback(self._cbGetChatInfoForInvite, user, moreTLVs[12]))
                else:
                    self.services[SERVICE_CHATNAV].getChatInfo(exchange, name, instance).\
                        addCallback(self._cbGetChatInfoForInvite, user, moreTLVs[12])
            elif requestClass == CAP_SEND_FILE:
                if moreTLVs.has_key(11): # cancel
                    log.msg('cancelled file request')
                    log.msg(status)
                    return # handle this later
                if moreTLVs.has_key(10001):
                    name = moreTLVs[10001][9:-7]
                    desc = moreTLVs[12]
                    log.msg('file request from %s, %s, %s' % (user, name, desc))
                    self.receiveSendFileRequest(user, name, desc, cookie)
            else:
                log.msg('unsupported rendezvous: %s' % requestClass)
                log.msg(repr(moreTLVs))
        elif channel == 4:
            for k,v in tlvs.items():
                if k == 5:
                    # message data
                    uinHandle = struct.unpack("<I", v[:4])[0]
                    uin = "%s"%uinHandle
                    messageType = ord(v[4])
                    messageFlags = ord(v[5])
                    messageStringLength = struct.unpack("<H", v[6:8])[0]
                    messageString = v[8:8+messageStringLength]
                    message = [messageString]
                    #log.msg("type = %d" % (messageType))
                    #log.msg("uin = %s" % (uin))
                    #log.msg("flags = %d" % (messageFlags))
                    #log.msg("strlen = %d" % (messageStringLength))
                    #log.msg("msg = %s" % (messageString))
                    if messageType == 0x01:
                        # old style message
                        flags = []
                        multiparts = []
                        if messageStringLength > 0: multiparts.append(tuple(message))
                        self.receiveMessage(user, multiparts, flags)
                    elif messageType == 0x06:
                        # authorization request
                        self.gotAuthorizationRequest(uin)
                    elif messageType == 0x07:
                        # authorization denied
                        self.gotAuthorizationResponse(uin, False)
                    elif messageType == 0x08:
                        # authorization ok
                        self.gotAuthorizationResponse(uin, True)
        else:
            log.msg('unknown channel %02x' % channel)
            log.msg(tlvs)

    def oscar_04_14(self, snac):
        """
        client/server typing notifications
        """
        data = snac[3]
        scrnnamelen = int(struct.unpack('B',data[10:11])[0])
        scrnname = str(data[11:11+scrnnamelen])
        typestart = 11+scrnnamelen+1
        type = struct.unpack('B', data[typestart])[0]
        tlvs = dict()
        user = OSCARUser(scrnname, None, tlvs)

        if (type == 0x02):
            self.receiveTypingNotify("begin", user)
        elif (type == 0x01):
            self.receiveTypingNotify("idle", user)
        elif (type == 0x00):
            self.receiveTypingNotify("finish", user)

    def _cbGetChatInfoForInvite(self, info, user, message):
        apply(self.receiveChatInvite, (user,message)+info)

    def oscar_09_03(self, snac):
        """
        BOS rights response
        """
        tlvs = readTLVs(snac[3])
        self.maxPermitList = tlvs[1]
        self.maxDenyList = tlvs[2]

    def oscar_0B_02(self, snac):
        """
        stats reporting interval
        """
        self.reportingInterval = struct.unpack('!H',snac[3][:2])[0]

    def oscar_13_03(self, snac):
        """
        SSI rights response
        """
        #tlvs = readTLVs(snac[3])
        pass # we don't know how to parse this

    def oscar_13_0E(self, snac):
        """
        SSI modification response
        """
        #tlvs = readTLVs(snac[3])
        pass # we don't know how to parse this

    def oscar_13_19(self, snac):
        """
        Got authorization request
        """
        pos = 0
        #if 0x80 & snac[0] or 0x80 & snac[1]:
        #    sLen,id,length = struct.unpack(">HHH", snac[3][:6])
        #    pos = 6 + length
        uinlen = ord(snac[3][pos])
        pos += 1
        uin = snac[3][pos:pos+uinlen]
        pos += uinlen
        self.gotAuthorizationRequest(uin)

    def oscar_13_1B(self, snac):
        """
        Got authorization response
        """
        pos = 0
        #if 0x80 & snac[0] or 0x80 & snac[1]:
        #    sLen,id,length = struct.unpack(">HHH", snac[3][:6])
        #    pos = 6 + length
        uinlen = ord(snac[3][pos])
        pos += 1
        uin = snac[3][pos:pos+uinlen]
        pos += uinlen
        success = ord(snac[3][pos])
        pos += 1
        reasonlen = struct.unpack(">H", snac[3][pos:pos+2])[0]
        pos += 2
        reason = snac[3][pos:]
        if success:
            # authorization request successfully granted
            self.gotAuthorizationResponse(uin, True)
        else:
            # authorization request was not granted
            self.gotAuthorizationResponse(uin, False)

    def oscar_13_1C(self, snac):
        """
        SSI Your were added to someone's buddylist
        """
        pos = 0
        #if 0x80 & snac[0] or 0x80 & snac[1]:
        #    sLen,id,length = struct.unpack(">HHH", snac[3][:6])
        #    pos = 6 + length
        #    val = snac[3][4:pos]
        uinLen = ord(snac[3][pos])
        uin = snac[3][pos+1:pos+1+uinLen]
        self.youWereAdded(uin)

    # methods to be called by the client, and their support methods
    def requestSelfInfo(self):
        """
        ask for the OSCARUser for ourselves
        """
        d = defer.Deferred()
        d.addErrback(self._ebDeferredSelfInfoError)
        self.sendSNAC(0x01, 0x0E, '').addCallback(self._cbRequestSelfInfo, d)
        return d

    def _ebDeferredSelfInfoError(self, error):
        log.msg('ERROR IN SELFINFO DEFERRED %s' % error)

    def _cbRequestSelfInfo(self, snac, d):
        self.receivedSelfInfo(self.parseUser(snac[5]))
        #d.callback(self.parseUser(snac[5]))

    def oscar_15_03(self, snac):
        """
        Meta information (Offline messages, extended info about users)
        """
        tlvs = readTLVs(snac[3])
        for k, v in tlvs.items():
            if (k == 1):
                targetuin,type = struct.unpack('<IH',v[2:8])
                if (type == 0x41):
                    # Offline message
                    senderuin = struct.unpack('<I',v[10:14])[0]
                    #print "senderuin: "+str(senderuin)+"\n"
                    msg_date = str( "%4d-%02d-%02d %02d:%02d"
                                    % struct.unpack('<HBBBB', v[14:20]) )
                    messagetype, messageflags,messagelen = struct.unpack('<BBH',v[20:24])
                    message = [ str( v[24:24+messagelen-1] )
                                + "\n\n/sent " + msg_date ]

                    if (messagelen > 0):
                        flags = []
                        multiparts = []
                        tlvs = dict()
                        multiparts.append(tuple(message))
                        user = OSCARUser(str(senderuin), None, tlvs)
                        self.receiveMessage(user, multiparts, flags)
                elif (type == 0x42):
                    # End of offline messages
                    reqdata = '\x08\x00'+struct.pack("<I",int(self.username))+'\x3e\x00\x02\x00'
                    tlvs = TLV(0x01, reqdata)
                    self.sendSNAC(0x15, 0x02, tlvs)
                elif (type == 0x7da):
                    # Meta information
                    # print [ "%x" % ord(n) for n in v ]
                    sequenceNumber,rType,success = struct.unpack("<HHB",v[8:13])
                    if success == 0x0a:
                        if rType == 0xc8:
                            # SNAC(15,03)/07DA/00C8 | META_BASIC_USERINFO
                            # http://iserverd1.khstu.ru/oscar/snac_15_03_07da_00c8.html
                            nick,first,last,email,homeCity,homeState,homePhone,homeFax,homeAddress,cellPhone,homeZip,homeCountry = self.parseFullInfo(v[13:])
                            self.gotUserInfo(sequenceNumber, rType, [nick,first,last,email,homeCity,homeState,homePhone,homeFax,homeAddress,cellPhone,homeZip,homeCountry])
                        elif rType == 0xdc:
                            # SNAC(15,03)/07DA/00DC | META_MORE_USERINFO
                            # http://iserverd1.khstu.ru/oscar/snac_15_03_07da_00dc.html
                            homepage,birth = self.parseMoreInfo(v[13:])
                            self.gotUserInfo(sequenceNumber, rType, [homepage,birth])
                        elif rType == 0xeb or rType == 0x10e or rType == 0xf0 or rType == 0xfa:
                            # for now we don't care about these
                            self.gotUserInfo(sequenceNumber, rType, None)
                        elif rType == 0xd2:
                            # SNAC(15,03)/07DA/00D2 | META_WORK_USERINFO
                            # http://iserverd1.khstu.ru/oscar/snac_15_03_07da_00d2.html
                            city,state,phone,fax,address,zip,country,company,department,position = self.parseWorkInfo(v[13:])
                            self.gotUserInfo(sequenceNumber, rType, [city,state,phone,fax,address,zip,country,company,department,position])
                        elif rType == 0xe6:
                            # SNAC(15,03)/07DA/00E6 | META_NOTES_USERINFO
                            # http://iserverd1.khstu.ru/oscar/snac_15_03_07da_00e6.html
                            usernotes = self.parseNotesInfo(v[13:])
                            self.gotUserInfo(sequenceNumber, rType, [usernotes])
                    else:
                        self.gotUserInfo(sequenceNumber, 0xffff, None)
                else:
                    # can there be anything else
                    pass
            elif (k == 2):
                pass
            elif (k == 3):
                pass
            #else:
            #    print str(k)+":::"+str(v)+"\n"

    def initSSI(self):
        """
        this sends the rate request for family 0x13 (Server Side Information)
        so we can then use it
        """
        return self.sendSNAC(0x13, 0x02, '').addCallback(self._cbInitSSI)

    def _cbInitSSI(self, snac, d):
        return {} # don't even bother parsing this

    def requestSSI(self, timestamp = 0, revision = 0):
        """
        request the server side information
        if the deferred gets None, it means the SSI is the same
        """
        return self.sendSNAC(0x13, 0x05,
            struct.pack('!LH',timestamp,revision)).addCallback(self._cbRequestSSI)

    def _cbRequestSSI(self, snac, args = ()):
        if snac[1] == 0x0f: # same SSI as we have
            return
        itemdata = snac[5][3:]
        if args:
            revision, groups, permit, deny, permitMode, visibility, iconcksum = args
        else:
            version, revision = struct.unpack('!BH', snac[5][:3])
            groups = {}
            permit = []
            deny = []
            permitMode = None
            visibility = None
            iconcksum = []
        while len(itemdata)>4:
            nameLength = struct.unpack('!H', itemdata[:2])[0]
            name = itemdata[2:2+nameLength]
            groupID, buddyID, itemType, restLength = \
                struct.unpack('!4H', itemdata[2+nameLength:10+nameLength])
            tlvs = readTLVs(itemdata[10+nameLength:10+nameLength+restLength])
            itemdata = itemdata[10+nameLength+restLength:]
            if itemType == AIM_SSI_TYPE_BUDDY: # buddies
                groups[groupID].addUser(buddyID, SSIBuddy(name, groupID, buddyID, tlvs))
            elif itemType == AIM_SSI_TYPE_GROUP: # group
                g = SSIGroup(name, groupID, buddyID, tlvs)
                if groups.has_key(0): groups[0].addUser(groupID, g)
                groups[groupID] = g
            elif itemType == AIM_SSI_TYPE_PERMIT: # permit
                permit.append(name)
            elif itemType == AIM_SSI_TYPE_DENY: # deny
                deny.append(name)
            elif itemType == AIM_SSI_TYPE_PDINFO: # permit deny info
                if tlvs.has_key(0xca):
                    permitMode = {0x01:'permitall',0x02:'denyall',0x03:'permitsome',0x04:'denysome',0x05:'permitbuddies'}.get(ord(tlvs[0xca]),None)
                if tlvs.has_key(0xcb):
                    visibility = {'\xff\xff\xff\xff':'all','\x00\x00\x00\x04':'notaim'}.get(tlvs[0xcb],None)
            elif itemType == AIM_SSI_TYPE_PRESENCEPREFS: # presence preferences
                pass
            elif itemType == AIM_SSI_TYPE_ICQSHORTCUT: # ICQ2K shortcuts bar?
                pass
            elif itemType == AIM_SSI_TYPE_IGNORE: # Ignore list record
                pass
            elif itemType == AIM_SSI_TYPE_LASTUPDATE: # Last update time
                pass
            elif itemType == AIM_SSI_TYPE_SMS: # SMS contact. Like 1#EXT, 2#EXT, etc
                pass
            elif itemType == AIM_SSI_TYPE_IMPORTTIME: # Roster import time
                pass
            elif itemType == AIM_SSI_TYPE_ICONINFO: # icon information
                # I'm not sure why there are multiple of these sometimes
                # We're going to return all of them though...
                iconcksum.append(SSIIconSum(name, groupID, buddyID, tlvs))
            else:
                log.msg('unknown SSI entry: %s %s %s %s %s' % (name, groupID, buddyID, itemType, tlvs))
        timestamp = struct.unpack('!L',itemdata)[0]
        if not timestamp: # we've got more packets coming
            # which means add some deferred stuff
            d = defer.Deferred()
            self.requestCallbacks[snac[4]] = d
            d.addCallback(self._cbRequestSSI, (revision, groups, permit, deny, permitMode, visibility, iconcksum))
            d.addErrback(self._ebDeferredRequestSSIError, revision, groups, permit, deny, permitMode, visibility, iconcksum)
            return d
        if (len(groups) <= 0):
            gusers = None
        else:
            gusers = groups[0].users
        return (gusers,permit,deny,permitMode,visibility,iconcksum,timestamp,revision)

    def _ebDeferredRequestSSIError(self, error, revision, groups, permit, deny, permitMode, visibility, iconcksum):
        log.msg('ERROR IN REQUEST SSI DEFERRED %s' % error)

    def activateSSI(self):
        """
        activate the data stored on the server (use buddy list, permit deny settings, etc.)
        """
        self.sendSNACnr(0x13,0x07,'')

    def startModifySSI(self):
        """
        tell the OSCAR server to be on the lookout for SSI modifications
        """
        self.sendSNACnr(0x13,0x11,'')

    def addItemSSI(self, item):
        """
        add an item to the SSI server.  if buddyID == 0, then this should be a group.
        this gets a callback when it's finished, but you can probably ignore it.
        """
        d = self.sendSNAC(0x13,0x08, item.oscarRep())
        log.msg("addItemSSI: adding %s, g:%d, u:%d"%(item.name, item.groupID, item.buddyID))
        d.addCallback(self._cbAddItemSSI, item)
        return d

    def _cbAddItemSSI(self, snac, item):
        pos = 0
        #if snac[2] & 0x80 or snac[3] & 0x80:
        #    sLen,id,length = struct.unpack(">HHH", snac[5][:6])
        #    pos = 6 + length
        if snac[5][pos:pos+2] == "\00\00":
# success
#                data = struct.pack(">H", len(groupName))+groupName
#                data += struct.pack(">HH", 0, 1)
#                tlvData = TLV(0xc8, struct.pack(">H", buddyID))
#                data += struct.pack(">H", len(tlvData))+tlvData
#                self.sendSNACnr(0x13,0x09, data)
            if item.buddyID != 0: # is it a buddy or a group?
                self.buddyAdded(item.name)
        elif snac[5][pos:pos+2] == "\00\x0a":
            # invalid, error while adding
            pass
        elif snac[5][pos:pos+2] == "\00\x0c":
            # limit exceeded
            self.errorMessage("Contact list limit exceeded")
        elif snac[5][pos:pos+2] == "\00\x0d":
            # Trying to add ICQ contact to an AIM list
            self.errorMessage("Trying to add ICQ contact to an AIM list")
        elif snac[5][pos:pos+2] == "\00\x0e":
            # requires authorization
            log.msg("Authorization needed... requesting")
            self.sendAuthorizationRequest(item.name, "Please authorize me")
            item.authorizationRequestSent = True
            item.authorized = False
            self.addItemSSI(item)

    def modifyItemSSI(self, item, groupID = None, buddyID = None):
        if groupID is None:
            if isinstance(item, SSIIconSum):
                groupID = 0
            elif isinstance(item, SSIGroup):
                groupID = 0
            else:
                groupID = item.group.group.findIDFor(item.group)
        if buddyID is None:
            if isinstance(item, SSIIconSum):
                buddyID = 0x5dd6
            elif hasattr(item, "group"):
                buddyID = item.group.findIDFor(item)
            else:
                buddyID = 0
        return self.sendSNAC(0x13,0x09, item.oscarRep())

    def delItemSSI(self, item):
        return self.sendSNAC(0x13,0x0A, item.oscarRep())

    def endModifySSI(self):
        self.sendSNACnr(0x13,0x12,'')

    def setProfile(self, profile=None):
        """
        set the profile.
        send None to not set a profile (different from '' for a blank one)
        """
        self.profile = profile
        tlvs = ''
        if self.profile is not None:
            tlvs =  TLV(1,'text/aolrtf; charset="us-ascii"') + \
                    TLV(2,self.profile)

        tlvs = tlvs + TLV(5, ''.join(self.capabilities))
        self.sendSNACnr(0x02, 0x04, tlvs)

    def setAway(self, away = None):
        """
        set the away message, or return (if away == None)
        """
        self.awayMessage = away
        tlvs = TLV(3,'text/aolrtf; charset="us-ascii"') + \
               TLV(4,away or '')
        self.sendSNACnr(0x02, 0x04, tlvs)

    def setBack(self, status=None):
        """
        set the extended status message
        """
        # If our away message is set, clear it.
        if self.awayMessage:
            self.setAway()
        
        if not status:
            status = ""
        else:
            status = status[:220]
               
        log.msg("Setting extended status message to \"%s\""%status)
        self.backMessage = status
        packet = struct.pack(
               "!HHHbbH",
               0x001d,         # H
               len(status)+8,  # H
               0x0002,         # H
               0x04,           # b
               len(status)+4,  # b
               len(status)     # H
        ) + str(status) + struct.pack("H",0x0000)
        
        self.sendSNACnr(0x01, 0x1e, packet)

    def sendAuthorizationRequest(self, uin, authString):
        """
        send an authorization request
        """
        packet = struct.pack("b", len(uin))
        packet += uin
        packet += struct.pack(">H", len(authString))
        packet += authString
        packet += struct.pack("H", 0x00)
        log.msg("sending authorization request to %s"%uin)
        self.sendSNACnr(0x13, 0x18, packet)

    def sendAuthorizationResponse(self, uin, success, responsString):
        """
        send an authorization response
        """
        packet  = struct.pack("b", len(uin)) + uin
        if success:
            packet += struct.pack("b", 1)
        else:
            packet += struct.pack("b", 0)
        packet += struct.pack(">H", len(responsString)) + responsString
        self.sendSNACnr(0x13, 0x1a, packet)

    def setICQStatus(self, status):
        """
        set status of user: online, away, xa, dnd or chat
        """
        if status == "away":
            icqStatus = 0x01
        elif status == "dnd":
            icqStatus = 0x02
        elif status == "xa":
            icqStatus = 0x04
        elif status == "chat":
            icqStatus = 0x20
        else:
            icqStatus = 0x00
        self.sendSNACnr(0x01, 0x1e, TLV(0x06, struct.pack(">HH", self.statusindicators, icqStatus)))

    def setIdleTime(self, idleTime):
        """
        set our idle time.  don't call more than once with a non-0 idle time.
        """
        self.sendSNACnr(0x01, 0x11, struct.pack('!L',idleTime))

    def sendMessage(self, user, message, wantAck = 0, autoResponse = 0, offline = 0 ):  \
                    #haveIcon = 0, ):
        """
        send a message to user (not an OSCARUseR).
        message can be a string, or a multipart tuple.
        if wantAck, we return a Deferred that gets a callback when the message is sent.
        if autoResponse, this message is an autoResponse, as if from an away message.
        if offline, this is an offline message (ICQ only, I think)
        """
        data = ''.join([chr(random.randrange(0, 127)) for i in range(8)]) # cookie
        data = data + '\x00\x01' + chr(len(user)) + user
        if not type(message) in (types.TupleType, types.ListType):
            message = [[message,]]
            if type(message[0][0]) == types.UnicodeType:
                message[0].append('unicode')
        messageData = ''
        for part in message:
            charSet = 0
            if 'unicode' in part[1:]:
                charSet = 2
                #part[0] = part[0].encode('utf-8')
                part[0] = part[0].encode('utf-16be', 'replace')
            elif 'iso-8859-1' in part[1:]:
                charSet = 3
                part[0] = part[0].encode('iso-8859-1', 'replace')
            elif 'none' in part[1:]:
                charSet = 0xffff
            if 'macintosh' in part[1:]:
                charSubSet = 0xb
            else:
                charSubSet = 0
            messageData = messageData + '\x01\x01' + \
                          struct.pack('!3H',len(part[0])+4,charSet,charSubSet)
            messageData = messageData + part[0]
        data = data.encode('iso-8859-1', 'replace') + TLV(2, '\x05\x01\x00\x03\x01\x01\x02'+messageData)
        if wantAck:
            data = data + TLV(3,'')
        if autoResponse:
            data = data + TLV(4,'')
        if offline:
            data = data + TLV(6,'')
        if wantAck:
            return self.sendSNAC(0x04, 0x06, data).addCallback(self._cbSendMessageAck, user, message)
        self.sendSNACnr(0x04, 0x06, data)

    def _cbSendMessageAck(self, snac, user, message):
        return user, message

    def sendInvite(self, user, chatroom, wantAck = 0):
        """
        send a chat room invitation to a user (not an OSCARUser).
        if wantAck, we return a Deferred that gets a callback when the message is sent.
        """
        cookie = ''.join([chr(random.randrange(0, 127)) for i in range(8)]) # cookie
        intdata = '\x00\x00'+cookie+CAP_CHAT
        intdata = intdata + TLV(0x0a,'\x00\x01')
        intdata = intdata + TLV(0x0f,'')
        intdata = intdata + TLV(0x0d,'us-ascii')
        intdata = intdata + TLV(0x0c,'Please join me in this Chat.')
        intdata = intdata + TLV(0x2711,struct.pack('!HB',chatroom.exchange,len(chatroom.fullName))+chatroom.fullName+struct.pack('!H',chatroom.instance))
        data = cookie+'\x00\x02'+chr(len(user))+user+TLV(5,intdata)
        if wantAck:
            data = data + TLV(3,'')
            return self.sendSNAC(0x04, 0x06, data).addCallback(self._cbSendInviteAck, user, chatroom)
        self.sendSNACnr(0x04, 0x06, data)

    def _cbSendInviteAck(self, snac, user, chatroom):
        return user, chatroom

    def connectService(self, service, wantCallback = 0, extraData = ''):
        """
        connect to another service
        if wantCallback, we return a Deferred that gets called back when the service is online.
        if extraData, append that to our request.
        """
        if wantCallback:
            d = defer.Deferred()
            d.addErrback(self._ebDeferredConnectServiceError)
            self.sendSNAC(0x01,0x04,struct.pack('!H',service) + extraData).addCallback(self._cbConnectService, d)
            return d
        else:
            self.sendSNACnr(0x01,0x04,struct.pack('!H',service))

    def _ebDeferredConnectServiceError(self, error):
        log.msg('ERROR IN CONNECT SERVICE DEFERRED %s' % error)

    def _cbConnectService(self, snac, d):
        if snac:
            #d.arm()
            # CHECKME, something was happening here involving getting a snac packet
            # that didn't have [2:] in it...
            self.oscar_01_05(snac[2:], d)
        else:
            self.connectionFailed()

    def createChat(self, shortName, exchange):
        """
        create a chat room
        """
        if self.services.has_key(SERVICE_CHATNAV):
            return self.services[SERVICE_CHATNAV].createChat(shortName,exchange)
        else:
            d = defer.Deferred()
            d.addErrback(self._ebDeferredCreateChatError)
            self.connectService(SERVICE_CHATNAV,1).addCallback(lambda s:s.createChat(shortName,exchange).chainDeferred(d))
            return d

    def _ebDeferredCreateChatError(self, error):
        log.msg('ERROR IN CREATE CHAT DEFERRED %s' % error)

    def joinChat(self, exchange, fullName, instance):
        """
        join a chat room
        """
        #d = defer.Deferred()
        return self.connectService(0x0e, 1, TLV(0x01, struct.pack('!HB',exchange, len(fullName)) + fullName +
                          struct.pack('!H', instance))).addCallback(self._cbJoinChat) #, d)
        #return d

    def _cbJoinChat(self, chat):
        del self.services[SERVICE_CHAT]
        return chat

    def warnUser(self, user, anon = 0):
        return self.sendSNAC(0x04, 0x08, '\x00'+chr(anon)+chr(len(user))+user).addCallback(self._cbWarnUser)

    def _cbWarnUser(self, snac):
        oldLevel, newLevel = struct.unpack('!2H', snac[5])
        return oldLevel, newLevel

    def getInfo(self, user):
        #if user.
        return self.sendSNAC(0x02, 0x05, '\x00\x01'+chr(len(user))+user).addCallback(self._cbGetInfo)

    def _cbGetInfo(self, snac):
        user, rest = self.parseUser(snac[5],1)
        tlvs = readTLVs(rest)
        return tlvs.get(0x02,None)

    def getProfile(self, user):
        #if user.
        return self.sendSNAC(0x02, 0x15, '\x00\x00\x00\x01'+chr(len(user))+user).addCallback(self._cbGetProfile).addErrback(self._cbGetProfileError)

    def _cbGetProfile(self, snac):
        user, rest = self.parseUser(snac[5],1)
        tlvs = readTLVs(rest)
        #encoding = tlvs[1]  We're ignoring this for now
        #profile = tlvs[2]  This is what we're after

        return tlvs.get(0x02,None)

    def _cbGetProfileError(self, result):
        return result

    def lookupEmail(self, email):
        #if email.
        return self.sendSNAC(0x0a, 0x02, email).addCallback(self._cbLookupEmail).addErrback(self._cbLookupEmailError)

    def _cbLookupEmail(self, snac):
        tlvs = readTLVs(snac[5])
        results = []
        data = snac[5]
        while data:
           tlv,data = readTLVs(data, count=1)
           results.append(tlv[0x01])

        return results

    def _cbLookupEmailError(self, result):
        return result

    def sendDirectorySearch(self, email=None, first=None, middle=None, last=None, maiden=None, nickname=None, address=None, city=None, state=None, zip=None, country=None, interest=None):
        """
        starts a directory search connection
        """
        #if self.services.has_key(SERVICE_DIRECTORY):
        #    if(email):
        #        return self.services[SERVICE_DIRECTORY].sendDirectorySearchByEmail(email)
        #    elif(interest):
        #        return self.services[SERVICE_DIRECTORY].sendDirectorySearchByInterest(interest)
        #    else:
        #        return self.services[SERVICE_DIRECTORY].sendDirectorySearchByNameAddr(first, middle, last, maiden, nickname, address, city, state, zip, country)
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredSendDirectorySearchError)
        if(email):
            self.connectService(SERVICE_DIRECTORY,1).addCallback(lambda s:s.sendDirectorySearchByEmail(email).chainDeferred(d))
        elif(interest):
            self.connectService(SERVICE_DIRECTORY,1).addCallback(lambda s:s.sendDirectorySearchByInterest(interest).chainDeferred(d))
        else:
            self.connectService(SERVICE_DIRECTORY,1).addCallback(lambda s:s.sendDirectorySearchByNameAddr(first, middle, last, maiden, nickname, address, city, state, zip, country).chainDeferred(d))
        return d

    def _ebDeferredSendDirectorySearchError(self, error):
        log.msg('ERROR IN SEND DIRECTORY SEARCH %s' % error)

    def sendInterestsRequest(self):
        """
        retrieves list of directory interests
        """
        #if self.services.has_key(SERVICE_DIRECTORY):
        #    return self.services[SERVICE_DIRECTORY].sendInterestsRequest()
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredSendInterestsRequestError)
        self.connectService(SERVICE_DIRECTORY,1).addCallback(lambda s:s.sendInterestsRequest().chainDeferred(d))
        return d

    def _ebDeferredSendInterestsRequestError(self, error):
        log.msg('ERROR IN SEND INTERESTS REQUEST %s' % error)

    def activateEmailNotification(self):
        """
        requests notification of email
        """
        if not self.services.has_key(SERVICE_EMAIL):
            self.connectService(SERVICE_EMAIL,1)

    def changePassword(self, oldpass, newpass):
        """
        changes a user's password
        """
        #if self.services.has_key(SERVICE_ADMIN):
        #    return self.services[SERVICE_ADMIN].changePassword(oldpass, newpass)
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredChangePasswordError)
        self.connectService(SERVICE_ADMIN,1).addCallback(lambda s:s.changePassword(oldpass, newpass).chainDeferred(d))
        return d

    def _ebDeferredChangePasswordError(self, error):
        log.msg('ERROR IN CHANGE PASSWORD %s' % error)

    def changeEmail(self, email):
        """
        changes a user's registered email address
        """
        #if self.services.has_key(SERVICE_ADMIN):
        #    return self.services[SERVICE_ADMIN].setEmailAddress(email)
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredChangeEmailError)
        self.connectService(SERVICE_ADMIN,1).addCallback(lambda s:s.setEmailAddress(email).chainDeferred(d))
        return d

    def _ebDeferredChangeEmailError(self, error):
        log.msg('ERROR IN CHANGE EMAIL %s' % error)

    def changeScreenNameFormat(self, formatted):
        """
        changes a user's screen name format
        note that only the spacing and capitalization can be changed
        """
        #if self.services.has_key(SERVICE_ADMIN):
        #    return self.services[SERVICE_ADMIN].formatScreenName(formatted)
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredFormatSNError)
        self.connectService(SERVICE_ADMIN,1).addCallback(lambda s:s.formatScreenName(formatted).chainDeferred(d))
        return d

    def _ebDeferredFormatSNError(self, error):
        log.msg('ERROR IN FORMAT SCREEN NAME %s' % error)

    def getFormattedScreenName(self):
        """
        retrieves the user's formatted screen name
        """
        #if self.services.has_key(SERVICE_ADMIN):
        #    return self.services[SERVICE_ADMIN].requestFormattedScreenName()
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredGetSNError)
        self.connectService(SERVICE_ADMIN,1).addCallback(lambda s:s.requestFormattedScreenName().chainDeferred(d))
        return d

    def _ebDeferredGetSNError(self, error):
        log.msg('ERROR IN SCREEN NAME RETRIEVAL %s' % error)

    def getEmailAddress(self):
        """
        retrieves the user's registered email address
        """
        #if self.services.has_key(SERVICE_ADMIN):
        #    return self.services[SERVICE_ADMIN].requestEmailAddress()
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredGetEmailError)
        self.connectService(SERVICE_ADMIN,1).addCallback(lambda s:s.requestEmailAddress().chainDeferred(d))
        return d

    def _ebDeferredGetEmailError(self, error):
        log.msg('ERROR IN EMAIL ADDRESS RETRIEVAL %s' % error)

    def confirmAccount(self):
        """
        requests email to be sent to registered address for confirmation
        of account
        """
        #if self.services.has_key(SERVICE_ADMIN):
        #    return self.services[SERVICE_ADMIN].requestAccountConfirm()
        #else:
        d = defer.Deferred()
        d.addErrback(self._ebDeferredConfirmAccountError)
        self.connectService(SERVICE_ADMIN,1).addCallback(lambda s:s.requestAccountConfirm().chainDeferred(d))
        return d

    def _ebDeferredConfirmAccountError(self, error):
        log.msg('ERROR IN ACCOUNT CONFIRMATION RETRIEVAL %s' % error)

    def sendBuddyIcon(self, iconData, iconLen):
        """
        uploads a buddy icon
        """
        d = defer.Deferred()
        d.addErrback(self._ebDeferredSendBuddyIconError)
        self.connectService(SERVICE_SSBI,1).addCallback(lambda s:s.uploadIcon(iconData, iconLen).chainDeferred(d))
        return d

    def _ebDeferredSendBuddyIconError(self, error):
        log.msg('ERROR IN SEND BUDDY ICON %s' % error)

    def retrieveBuddyIcon(self, contact, hash, flags):
        """
        retrieves a buddy icon
        """
        d = defer.Deferred()
        d.addErrback(self._ebDeferredRetrieveBuddyIconError)
        self.connectService(SERVICE_SSBI,1).addCallback(lambda s:s.retrieveAIMIcon(contact, hash, flags).chainDeferred(d))
        return d

    def _ebDeferredRetrieveBuddyIconError(self, error):
        log.msg('ERROR IN RETRIEVE BUDDY ICON %s' % error)

    def getMetaInfo(self, user, id):
        #if user.
        #reqdata = struct.pack("I",int(self.username))+'\xd0\x07\x08\x00\xba\x04'+struct.pack("I",int(user))
        reqdata = struct.pack("<I",int(self.username))+'\xd0\x07'+ struct.pack("<H",id) +'\xb2\x04'+struct.pack("<I",int(user))
        data = struct.pack("<H",14)+reqdata
        tlvs = TLV(0x01, data)
        #return self.sendSNAC(0x15, 0x02, tlvs).addCallback(self._cbGetMetaInfo)
        return self.sendSNACnr(0x15, 0x02, tlvs)

    #def _cbGetMetaInfo(self, snac):
    #    nick,first,last,email = self.parseBasicInfo(snac[5][16:])
#     return [nick,first,last,email]

    def requestOffline(self):
        """
        request offline messages
        """
        reqdata = '\x08\x00'+struct.pack("<I",int(self.username))+'\x3c\x00\x02\x00'
        tlvs = TLV(0x01, reqdata)
        return self.sendSNACnr(0x15, 0x02, tlvs)
  
    #def _cbreqOffline(self, snac):
        #print "arg"

    def sendTypingNotification(self, user, type):
        #if user.
        return self.sendSNAC(0x04, 0x14, '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01'+chr(len(user))+user+type)

    def getAway(self, user):
        return self.sendSNAC(0x02, 0x05, '\x00\x03'+chr(len(user))+user).addCallback(self._cbGetAway)

    def _cbGetAway(self, snac):
        user, rest = self.parseUser(snac[5],1)
        tlvs = readTLVs(rest)
        return [tlvs.get(0x03,None),tlvs.get(0x04,None)] # return None if there is no away message

    #def acceptSendFileRequest(self,

    # methods to be overriden by the client
    def initDone(self):
        """
        called when we get the rate information, which means we should do other init. stuff.
        """
        log.msg('%s initDone' % self)
        pass

    def gotUserInfo(self, id, type, userinfo):
        """
        called when a user info packet is received
        """
        pass

    def gotAuthorizationResponse(self, uin, success):
        """
        called when a user sends an authorization response
        """
        pass

    def gotAuthorizationRequest(self, uin):
        """
        called when a user want's an authorization
        """
        pass

    def youWereAdded(self, uin):
        """
        called when a user added you to contact list
        """
        pass

    def buddyAdded(self, uin):
        """
        called when a buddy is added
        """
        pass

    def updateBuddy(self, user):
        """
        called when a buddy changes status, with the OSCARUser for that buddy.
        """
        log.msg('%s updateBuddy %s' % (self, user))
        pass

    def offlineBuddy(self, user):
        """
        called when a buddy goes offline
        """
        log.msg('%s offlineBuddy %s' % (self, user))
        pass

    def receiveMessage(self, user, multiparts, flags):
        """
        called when someone sends us a message
        """
        pass

    def receiveWarning(self, newLevel, user):
        """
        called when someone warns us.
        user is either None (if it was anonymous) or an OSCARUser
        """
        pass

    def receiveTypingNotify(self, type, user):
        """
        called when a typing notification occurs.
        type can be "begin", "idle", or "finish".
        user is an OSCARUser.
        """
        pass

    def errorMessage(self, message):
        """
        called when an error message should be signaled
        """
        pass

    def receiveChatInvite(self, user, message, exchange, fullName, instance, shortName, inviteTime):
        """
        called when someone invites us to a chat room
        """
        pass

    def chatReceiveMessage(self, chat, user, message):
        """
        called when someone in a chatroom sends us a message in the chat
        """
        pass

    def chatMemberJoined(self, chat, member):
        """
        called when a member joins the chat
        """
        pass

    def chatMemberLeft(self, chat, member):
        """
        called when a member leaves the chat
        """
        pass

    def chatInvitationAccepted(self, user):
        """
        called when a chat invitation we issued is accepted
        """
        pass

    def receiveSendFileRequest(self, user, file, description, cookie):
        """
        called when someone tries to send a file to us
        """
        pass

    def emailNotificationReceived(self, addr, url, unreadmsgs, hasunread):
        """
        called when the status of our email account changes
        """
        pass

    def receivedSelfInfo(self, user):
        """
        called when we receive information about ourself
        """
        pass

    def requestBuddyIcon(self, iconhash):
        """
        called when the server wants our buddy icon
        """
        pass



class OSCARService(SNACBased):
    def __init__(self, bos, cookie, d = None):
        SNACBased.__init__(self, cookie)
        self.bos = bos
        self.d = d

    def connectionLost(self, reason):
        for k,v in self.bos.services.items():
            if v == self:
                del self.bos.services[k]
                return

    def clientReady(self):
        SNACBased.clientReady(self)
        if self.d:
            self.d.callback(self)
            self.d = None


class ChatNavService(OSCARService):
    snacFamilies = {
        0x01:(3, 0x0010, 0x0629),
        0x0d:(1, 0x0010, 0x0629)
    }
    def oscar_01_07(self, snac):
        # rate info
        self.sendSNACnr(0x01, 0x08, '\000\001\000\002\000\003\000\004\000\005')
        self.sendSNACnr(0x0d, 0x02, '')

    def oscar_0D_09(self, snac):
        self.clientReady()

    def getChatInfo(self, exchange, name, instance):
        d = defer.Deferred()
        #d.addErrback(self._ebDeferredRequestSSIError)
        self.sendSNAC(0x0d,0x04,struct.pack('!HB',exchange,len(name)) + \
                      name + struct.pack('!HB',instance,2)). \
            addCallback(self._cbGetChatInfo, d)
        return d

    def _cbGetChatInfo(self, snac, d):
        data = snac[5][4:]
        exchange, length = struct.unpack('!HB',data[:3])
        fullName = data[3:3+length]
        instance = struct.unpack('!H',data[3+length:5+length])[0]
        tlvs = readTLVs(data[8+length:])
        shortName = tlvs[0x6a]
        inviteTime = struct.unpack('!L',tlvs[0xca])[0]
        info = (exchange,fullName,instance,shortName,inviteTime)
        d.callback(info)

    def createChat(self, shortName, exchange):
        #d = defer.Deferred()
        data = struct.pack('!H',exchange)
        # '\x00\x04'
        data = data + '\x06create\xff\xff\x01\x00\x03'
        data = data + TLV(0xd7, 'en')
        data = data + TLV(0xd6, 'us-ascii')
        data = data + TLV(0xd3, shortName)
        return self.sendSNAC(0x0d, 0x08, data).addCallback(self._cbCreateChat)
        #return d

    def _cbCreateChat(self, snac): #d):
        exchange, length = struct.unpack('!HB',snac[5][4:7])
        fullName = snac[5][7:7+length]
        instance = struct.unpack('!H',snac[5][7+length:9+length])[0]
        #d.callback((exchange, fullName, instance))
        return exchange, fullName, instance


class ChatService(OSCARService):
    snacFamilies = {
        0x01:(3, 0x0010, 0x0629),
        0x0E:(1, 0x0010, 0x0629)
    }
    def __init__(self,bos,cookie, d = None):
        OSCARService.__init__(self,bos,cookie,d)
        self.exchange = None
        self.fullName = None
        self.instance = None
        self.name = None
        self.members = None

    clientReady = SNACBased.clientReady # we'll do our own callback

    def oscar_01_07(self,snac):
        self.sendSNAC(0x01,0x08,"\000\001\000\002\000\003\000\004\000\005")
        self.clientReady()

    def oscar_0E_02(self, snac):
#        try: # this is EVIL
#            data = snac[3][4:]
#            self.exchange, length = struct.unpack('!HB',data[:3])
#            self.fullName = data[3:3+length]
#            self.instance = struct.unpack('!H',data[3+length:5+length])[0]
#            tlvs = readTLVs(data[8+length:])
#            self.name = tlvs[0xd3]
#            self.d.callback(self)
#        except KeyError:
        data = snac[3]
        self.exchange, length = struct.unpack('!HB',data[:3])
        self.fullName = data[3:3+length]
        self.instance = struct.unpack('!H',data[3+length:5+length])[0]
        tlvs = readTLVs(data[8+length:])
        self.name = tlvs[0xd3]
        self.d.callback(self)

    def oscar_0E_03(self,snac):
        users=[]
        rest=snac[3]
        while rest:
            user, rest = self.bos.parseUser(rest, 1)
            users.append(user)
        if not self.fullName:
            self.members = users
        else:
            self.members.append(users[0])
            self.bos.chatMemberJoined(self,users[0])

    def oscar_0E_04(self,snac):
        user=self.bos.parseUser(snac[3])
        for u in self.members:
            if u.name == user.name: # same person!
                self.members.remove(u)
        self.bos.chatMemberLeft(self,user)

    def oscar_0E_06(self,snac):
        data = snac[3]
        user,rest=self.bos.parseUser(snac[3][14:],1)
        tlvs = readTLVs(rest[8:])
        message=tlvs[1]
        self.bos.chatReceiveMessage(self,user,message)

    def sendMessage(self,message):
        log.msg("Sending chat message... I hope.")
        tlvs=TLV(0x02,"us-ascii")+TLV(0x03,"en")+TLV(0x01,message)
        data = ''.join([chr(random.randrange(0, 127)) for i in range(8)]) # cookie
        data = data + "\x00\x03" # message channel 3
        data = data + TLV(1, '') # this is for a chat room
        data = data + TLV(6, '') # reflect message back to us
        data = data + TLV(5, tlvs) # our actual message data
        self.sendSNACnr(0x0e, 0x05, data)
        #self.sendSNAC(0x0e,0x05,
        #              "\x46\x30\x38\x30\x44\x00\x63\x00\x00\x03\x00\x01\x00\x00\x00\x06\x00\x00\x00\x05"+
        #              struct.pack("!H",len(tlvs))+
        #              tlvs)

    def leaveChat(self):
        self.disconnect()


class DirectoryService(OSCARService):
    snacFamilies = {
        0x01:(3, 0x0010, 0x0629),
        0x0f:(1, 0x0010, 0x0629)
    }

    def oscar_01_07(self,snac):
        self.sendSNAC(0x01,0x08,"\000\001\000\002\000\003\000\004\000\005")
        self.clientReady()

    def sendDirectorySearchByEmail(self, email):
        #if email.
        # 00 1c 00 08 75 73 2d 61 73 63 69 69 00 0a 00 02 00 01 00 05
        # .  .  .  .  u  s  -  a  s  c  i  i  .  .  .  .  .  .  .  .

        # 00 13 6a 61 64 65 73 74 6f 72 6d 40 6e 63 2e 72 72 2e 63 6f 6d
        # .  .  j  a  d  e  s  t  o  r  m  @  n  c  .  r  r  .  c  o  m

        # 00 0a = standard
        # 00 02 = standard
        # 00 01 =
        # 00 05 = (email address?)
        # 00 13 = length

        return self.sendSNAC(0x0f, 0x02, '\x00\x1c\x00\x08us-ascii\x00\x0a\x00\x02\x00\x01'+TLV(0x05, email)).addCallback(self._cbGetDirectoryInfo).addErrback(self._cbGetDirectoryError)

    def sendDirectorySearchByNameAddr(self, first=None, middle=None, last=None, maiden=None, nickname=None, address=None, city=None, state=None, zip=None, country=None):
        # Must give at least a first or last name, all others optional

        # 00 1c 00 08 75 73 2d 61 73 63 69 69 00 0a 00 02 00 00 00 01
        # .  .  .  .  u  s  -  a  s  c  i  i  .  .  .  .  .  .  .  .

        # 00 06 44 61 6e 69 65 6c 00 02 00 09 48 65 6e 6e 69 6e 67 65 72
        # .  .  D  a  n  i  e  l  .  .  .  .  H  e  n  n  i  n  g  e  r

        # 00 0a = standard
        # 00 02 = standard
        # 00 00 =

        # 00 01 = (first name?)
        # 00 06 = length

        # 00 02 = (last name?)
        # 00 09 = length


        # All fields entered:

        # 00 1c 00 08 75 73 2d 61 73 63 69 69 00 0a 00 02 00 00 00 01
        # .  .  .  .  u  s  -  a  s  c  i  i  .  .  .  .  .  .  .  .

        # 00 06 44 61 6e 69 65 6c 00 02 00 09 48 65 6e 6e 69 6e 67 65 72
        # .  .  D  a  n  i  e  l  .  .  .  .  H  e  n  n  i  n  g  e  r

        # 00 03 00 04 41 64 61 6d 00 04 00 0a 48 65 6e 6e 69 63 67 74 6f
        # .  .  .  .  A  d  a  m  .  .  .  .  H  e  n  n  i  n  g  t  o

        # 6e 00 06 00 02 55 53 00 07 00 02 4e 43 00 08 00 06 47 61 72 6e
        # n  .  .  .  .  U  S  .  .  .  .  N  C  .  .  .  .  G  a  r  n

        # 65 72 00 0c 00 05 4e 69 6e 6a 61 00 0d 00 05 32 37 35 32 39 00
        # e  r  .  .  .  .  N  i  n  j  a  .  .  .  .  2  7  5  2  9  .

        # 21 00 13 31 30 35 20 42 72 6f 6f 6b 20 52 6f 63 6b 20 4c 61 6e
        # .  .  .  1  0  5     B  r  o  o  k     R  o  c  k     L  a  n

        # 65
        # e

        # 00 0a = standard
        # 00 02 = standard
        # 00 00 = unknown  0 for multi search, 1 for single entity search

        # then, type, length, value pairs
        # types
        # 00 01 = first name
        # 00 02 = last name
        # 00 03 = middle name
        # 00 04 = maiden name
        # 00 05 = email address
        # 00 06 = country (ab)
        # 00 07 = state (ab)
        # 00 08 = city
        # 00 0b = interest
        # 00 0c = nickname
        # 00 0d = zip code
        # 00 21 = street address

        snacData = '\x00\x1c\x00\x08us-ascii\x00\x0a\x00\x02\x00\x00'
        if (first): snacData = snacData + TLV(0x01, first)
        if (last): snacData = snacData + TLV(0x02, last)
        if (middle): snacData = snacData + TLV(0x03, middle)
        if (maiden): snacData = snacData + TLV(0x04, maiden)
        if (country): snacData = snacData + TLV(0x06, country)
        if (state): snacData = snacData + TLV(0x07, state)
        if (city): snacData = snacData + TLV(0x08, city)
        if (nickname): snacData = snacData + TLV(0x0c, nickname)
        if (zip): snacData = snacData + TLV(0x0d, zip)
        if (address): snacData = snacData + TLV(0x21, address)
        return self.sendSNAC(0x0f, 0x02, snacData).addCallback(self._cbGetDirectoryInfo).addErrback(self._cbGetDirectoryError)

    def sendDirectorySearchByInterest(self, interest):
        # official list of interests pulled from server

        # 00 1c 00 08 75 73 2d 61 73 63 69 69 00 0a 00 02 00 01 00 0b
        # .  .  .  .  u  s  -  a  s  c  i  i  .  .  .  .  .  .  .  .

        # 00 09 45 64 75 63 61 74 69 6f 6e
        # .  .  E  d  u  c  a  t  i  o  n

        # 00 0a = standard
        # 00 02 = standard
        # 00 01 =
        # 00 0b = (interest?)
        # 00 09 = length

        return self.sendSNAC(0x0f, 0x02, '\x00\x1c\x00\x08us-ascii\x00\x0a\x00\x02\x00\x01'+TLV(0x0b, interest)).addCallback(self._cbGetDirectoryInfo).addErrback(self._cbGetDirectoryError)

    def _cbGetDirectoryInfo(self, snac):
        #\x00\x07\x00\x00  if error?
        #\x00\x05\x00\x00  seems to be success
        #Got directory info [15, 3, 0, 0, 1L, '\x00\x05\x00\x00\x00\x01\x00\x01\x00\t\x00\x0cthejadestorm']
        #Received directory info [15, 3, 0, 0, 1L, '\x00\x07\x00\x00\x00\x01\x00\x01\x00\x04\x00\x12http://www.aol.com']
        log.msg("Received directory info %s" % snac)
        results = []
        snacData = snac[5]
        status,foo,num = struct.unpack('!HHH', snacData[0:6])
        if status == 0x07:
            # We have an error, typically this seems to mean directory server is unavailable, for now, return empty results
            log.msg("We received an error, returning empty results")
            return results
        elif status == 0x05:
            # We're good
            pass
        else:
            # Uhm.. what?  For not, return empty results
            log.msg("Directory info request returned status %s" % str(hex(status)))
            return results
        numresults = int(num)
        log.msg("Got directory info, %d results" % (numresults))
        cnt = 1
        data = snacData[6:]
        while cnt <= numresults:
            log.msg("  Data %s" % (repr(data)))
            numpieces = int(struct.unpack('>H', data[0:2])[0])
            tlvs,data = readTLVs(data[2:], count=numpieces)
            log.msg("  Entry %s" % (repr(tlvs)))
            result = {}
            if tlvs.has_key(0x0001): result['first'] = tlvs[0x0001]
            if tlvs.has_key(0x0002): result['last'] = tlvs[0x0002]
            if tlvs.has_key(0x0003): result['middle'] = tlvs[0x0003]
            if tlvs.has_key(0x0004): result['maiden'] = tlvs[0x0004]
            if tlvs.has_key(0x0005): result['email'] = tlvs[0x0005]
            if tlvs.has_key(0x0006): result['country'] = tlvs[0x0006]
            if tlvs.has_key(0x0007): result['state'] = tlvs[0x0007]
            if tlvs.has_key(0x0008): result['city'] = tlvs[0x0008]
            if tlvs.has_key(0x0009): result['screenname'] = tlvs[0x0009]
            if tlvs.has_key(0x000b): result['interest'] = tlvs[0x000b]
            if tlvs.has_key(0x000c): result['nickname'] = tlvs[0x000c]
            if tlvs.has_key(0x000d): result['zip'] = tlvs[0x000d]
            if tlvs.has_key(0x001c): result['region'] = tlvs[0x001c]
            if tlvs.has_key(0x0021): result['address'] = tlvs[0x0021]
            results.append(result)
            cnt = cnt + 1

        self.disconnect()
        return results

    def _cbGetDirectoryError(self, error):
        log.msg("Got directory error %s" % error)
        return error

    def sendInterestsRequest(self):
        return self.sendSNAC(0x0f, 0x04, "").addCallback(self._cbGetInterests).addErrback(self._cbGetInterestsError)

    def _cbGetInterests(self, snac):
        log.msg("Got interests %s" % snac)
        pass

    def _cbGetInterestsError(self, error):
        log.msg("Got interests error %s" % error)
        pass

    def disconnect(self):
        """
        send the disconnect flap, and sever the connection
        """
        self.sendFLAP('', 0x04)
        self.transport.loseConnection()


class EmailService(OSCARService):
    snacFamilies = {
        0x01:(3, 0x0010, 0x0629),
        0x18:(1, 0x0010, 0x0629)
    }

    def oscar_01_07(self,snac):
        self.sendSNAC(0x01,0x08,"\000\001\000\002\000\003\000\004\000\005")
        cookie1 = "\xb3\x80\x9a\xd8\x0d\xba\x11\xd5\x9f\x8a\x00\x60\xb0\xee\x06\x31"
        cookie2 = "\x5d\x5e\x17\x08\x55\xaa\x11\xd3\xb1\x43\x00\x60\xb0\xfb\x1e\xcb"
        self.sendSNAC(0x18, 0x06, "\x00\x02"+cookie1+cookie2)
        self.sendEmailRequest()
        self.nummessages = 0
        self.clientReady()

    def oscar_18_07(self,snac):
        snacData = snac[3]
        cookie1 = snacData[8:16]
        cookie2 = snacData[16:24]
        cnt = int(struct.unpack('>H', snacData[24:26])[0])
        tlvs,foo = readTLVs(snacData[26:], count=cnt)
        #0x80 = number of unread messages
        #0x81 = have new messages
        #0x82 = domain
        #0x84 = flag
        #0x07 = url to access
        #0x09 = username
        #0x1b = something about gateway
        #0x1d = some odd string
        #0x05 = apparantly an alert title
        #0x0d = apparantly an alert url
        domain = tlvs[0x82]
        username = tlvs[0x09]
        url = tlvs[0x07]
        unreadnum = int(struct.unpack('>H', tlvs[0x80])[0])
        hasunread = int(struct.unpack('B', tlvs[0x81])[0])
        log.msg("received email notify: tlvs = %s" % (str(tlvs)))
        self.bos.emailNotificationReceived('@'.join([username,domain]),
              str(url), unreadnum, hasunread)

    def sendEmailRequest(self):
        log.msg("Activating email notifications")
        self.sendSNAC(0x18, 0x16, "\x02\x04\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00")

    def disconnect(self):
        """
        send the disconnect flap, and sever the connection
        """
        self.sendFLAP('', 0x04)
        self.transport.loseConnection()


class AdminService(OSCARService):
    snacFamilies = {
        0x01:(3, 0x0010, 0x0629),
        0x07:(1, 0x0010, 0x0629)
    }

    def oscar_01_07(self,snac):
        self.sendSNAC(0x01,0x08,"\000\001\000\002\000\003\000\004\000\005")
        self.clientReady()

    def requestFormattedScreenName(self):
        return self.sendSNAC(0x07, 0x02, TLV(0x01, "")).addCallback(self._cbInfoResponse).addErrback(self._cbInfoResponseError)

    def requestEmailAddress(self):
        return self.sendSNAC(0x07, 0x02, TLV(0x11, "")).addCallback(self._cbInfoResponse).addErrback(self._cbInfoResponseError)

    def requestRegistrationStatus(self):
        return self.sendSNAC(0x07, 0x02, TLV(0x13, "")).addCallback(self._cbInfoResponse).addErrback(self._cbInfoResponseError)

    def changePassword(self, oldpassword, newpassword):
        return self.sendSNAC(0x07, 0x04, TLV(0x02, newpassword)+TLV(0x12, oldpassword)).addCallback(self._cbInfoResponse).addErrback(self._cbInfoResponseError)

    def formatScreenName(self, fmtscreenname):
        """ Note that the new screen name must be the same as the official
        one with only changes to spacing and capitalization """
        return self.sendSNAC(0x07, 0x04, TLV(0x01, fmtscreenname)).addCallback(self._cbInfoResponse).addErrback(self._cbInfoResponseError)

    def setEmailAddress(self, email):
        return self.sendSNAC(0x07, 0x04, TLV(0x11, email)).addCallback(self._cbInfoResponse).addErrback(self._cbInfoResponseError)

    def _cbInfoResponse(self, snac):
        """ This is sent for both changes and requests """
        log.msg("Got info change %s" % (snac))
        snacData = snac[5]
        perms = int(struct.unpack(">H", snacData[0:2])[0])
        tlvcnt = int(struct.unpack(">H", snacData[2:4])[0])
        tlvs,foo = readTLVs(snacData[4:], count=tlvcnt)
        log.msg("TLVS are %s" % str(tlvs))
        sn = tlvs.get(0x01, None)
        url = tlvs.get(0x04, None)
        error = tlvs.get(0x08, None)
        email = tlvs.get(0x11, None)
        if not error:
            errorret = None
        elif error == '\x00\x01':
            errorret = (error, "Unable to format screen name because the requested screen name differs from the original.")
        elif error == '\x00\x06':
            #errorret = (error, "Unable to format screen name because the requested screen name ends in a space.")
            errorret = (error, "Unable to format screen name because the requested screen name is too long.")
        elif error == '\x00\x0b':
            #I get the above on a 'too long' screen name.. so what's this really?
            errorret = (error, "Unable to format screen name because the requested screen name is too long.")
        elif error == '\x00\x1d':
            errorret = (error, "Unable to change email address because there is already a request pending for this screen name.")
        elif error == '\x00\x21':
            errorret = (error, "Unable to change email address because the given address has too many screen names associated with it.")
        elif error == '\x00\x23':
            errorret = (error, "Unable to change email address because the given address is invalid.")
        else:
            errorret = (error, "Unknown error code %d" % int(error))
        self.disconnect()
        return (perms, sn, url, errorret, email)

    def _cbInfoResponseError(self, error):
        log.msg("GOT INFO CHANGE ERROR %s" % error)
        self.disconnect()
        pass

    def requestAccountConfirm(self):
        """ Causes an email message to be sent to the registered email
        address.  By following the instructions in the email, you can
        get the trial/unconfirmed flag removed from your account. """
        return self.sendSNAC(0x07, 0x06, "").addCallback(self._cbAccountConfirm).addErrback(self._cbAccountConfirmError)

    def _cbAccountConfirm(self, snac):
        log.msg("Got account confirmation %s" % snac)
        status = int(struct.unpack(">H", snac[5][0:2])[0])
        # Returns whether it failed or not
        self.disconnect()
        if (status == "\x00\x13"):
            return 1
        else:
            return 0

    def _cbAccountConfirmError(self, error):
        log.msg("GOT ACCOUNT CONFIRMATION ERROR %s" % error)
        self.disconnect()

    def disconnect(self):
        """
        send the disconnect flap, and sever the connection
        """
        self.sendFLAP('', 0x04)
        self.transport.loseConnection()



class SSBIService(OSCARService):
    snacFamilies = {
        0x01:(3, 0x0010, 0x0629),
        0x10:(1, 0x0010, 0x0629)
    }

    def oscar_01_07(self,snac):
        self.sendSNAC(0x01,0x08,"\000\001\000\002\000\003\000\004\000\005")
        self.clientReady()

    def uploadIcon(self, iconData, iconLen):
        return self.sendSNAC(0x10, 0x02, struct.pack('!HH', 0x0001, iconLen)+iconData).addCallback(self._cbIconResponse).addErrback(self._cbIconResponseError)

    def _cbIconResponse(self, snac):
        log.msg("GOT ICON RESPONSE: %s" % str(snac))
        #\x05\x00\x00\x00\x00 - bad format?
        #\x04\x00\x00\x00\x00 - too large?
        #\x00\x00\x01\x01\x10 - ok, this is a hash, last one is length

        #checksumlen = (struct.unpack('!B', snac[4]))[0]
        #checksum = snac[1:1+checksumlen]
        self.disconnect()
        #return checksum
        return "Yeah ok"

    def _cbIconResponseError(self, error):
        log.msg("GOT UPLOAD ICON ERROR %s" % error)
        self.disconnect()

    def retrieveAIMIcon(self, contact, iconhash, iconflags):
        log.msg("Requesting icon for %s with hash %s" % (contact, binascii.hexlify(iconhash)))
        return self.sendSNAC(0x10, 0x04, struct.pack('!B', len(contact))+contact+"\x01\x00\x01"+struct.pack('!B', iconflags)+struct.pack('!B', len(iconhash))+iconhash).addCallback(self._cbAIMIconRequest).addErrback(self._cbAIMIconRequestError)

    def _cbAIMIconRequest(self, snac):
        #log.msg("Got Icon Request (AIM): %s" % (str(snac)))
        #\n
        #arlydwycka
        #\x00\x01
        #\x01
        #\x10
        #\xc7\x17`eF\x14\xc8\xd2l\xec\xf7\x9d\xcd\xe5\xde\x06
        #\x00\x00
        v = snac[5]
        scrnnamelen = int((struct.unpack('!B', v[0]))[0])
        #log.msg("scrnnamelen: %d" % scrnnamelen)
        scrnname = v[1:1+scrnnamelen]
        #log.msg("scrnname: %s" % scrnname)
        p = 1+scrnnamelen
        flags,iconcsumtype,iconcsumlen = struct.unpack('!HBB', v[p:p+4])
        iconcsumlen = int(iconcsumlen)
        p = p+4
        #log.msg("Where are we: %s" % binascii.hexlify(v[p:]))
        #\xc7\x17`eF\x14\xc8\xd2l\xec\xf7\x9d\xcd\xe5\xde\x06\x00\x00
        iconcsum = v[p:p+iconcsumlen]
        #log.msg("iconhash: %s" % binascii.hexlify(iconhash))
        p = p+iconcsumlen
        #log.msg("Where are we now: %s" % binascii.hexlify(v[p:]))
        iconlen = int((struct.unpack('!H', v[p:p+2]))[0])
        #log.msg("iconlen: %d" % iconlen)
        p = p + 2
        #log.msg("Where are we now: %s" % binascii.hexlify(v[p:]))
        #log.msg("The icon we can see is: %s" % binascii.hexlify(v[p:p+iconlen]))
        log.msg("Got Icon Request (AIM): %s, %s, %d" % (scrnname, binascii.hexlify(iconcsum), iconlen))
        if iconlen > 0 and iconlen != 90:
            icondata = v[p:p+iconlen]
        else:
            icondata = None
        self.disconnect()
        return (scrnname,iconcsumtype,iconcsum,iconlen,icondata)

    def _cbAIMIconRequestError(self, error):
        log.msg("GOT AIM ICON REQUEST ERROR %s" % error)
        self.disconnect()

    def disconnect(self):
        """
        send the disconnect flap, and sever the connection
        """
        self.sendFLAP('', 0x04)
        self.transport.loseConnection()



class OscarAuthenticator(OscarConnection):
    BOSClass = BOSConnection
    def __init__(self,username,password,deferred=None,icq=0):
        self.username=username
        self.password=password
        self.deferred=deferred
        self.icq=icq # icq mode is disabled
        #if icq and self.BOSClass==BOSConnection:
        #    self.BOSClass=ICQConnection

    def oscar_(self,flap):
        if not self.icq:
            self.sendFLAP("\000\000\000\001", 0x01)
            self.sendFLAP(SNAC(0x17,0x06,0,
                               TLV(TLV_USERNAME,self.username)+
                               TLV(0x004B,'')))
            self.state="Key"
        else:
            encpass=encryptPasswordICQ(self.password)
            self.sendFLAP('\000\000\000\001'+
                          TLV(0x01,self.username)+
                          TLV(0x02,encpass)+
                          TLV(0x03,'ICQ Inc. - Product of ICQ (TM).2001b.5.18.1.3659.85')+
                          TLV(0x16,"\x01\x0a")+
                          TLV(0x17,"\x00\x05")+
                          TLV(0x18,"\x00\x12")+
                          TLV(0x19,"\000\001")+
                          TLV(0x1a,"\x0eK")+
                          TLV(0x14,"\x00\x00\x00U")+
                          TLV(0x0f,"en")+
                          TLV(0x0e,"us"),0x01)
#            self.sendFLAP('\000\000\000\001'+
#                          TLV(0x01,self.username)+
#                          TLV(0x02,encpass)+
#                          TLV(0x03,'ICQ Inc. - Product of ICQ (TM).2003a.5.45.1.3777.85')+
#                          TLV(0x16,"\x01\x0a")+
#                          TLV(TLV_CLIENTMAJOR,"\x00\x05")+
#                          TLV(TLV_CLIENTMINOR,"\x00\x2d")+
#                          TLV(0x19,"\000\001")+
#                          TLV(TLV_CLIENTSUB,"\x0e\c1")+
#                          TLV(0x14,"\x00\x00\x00\x55")+
#                          TLV(0x0f,"en")+
#                          TLV(0x0e,"us"),0x01)
            self.state="Cookie"

    def oscar_Key(self,data):
        snac=readSNAC(data[1])
        if not snac:
            log.msg("Illegal SNAC data received in oscar_Key: %s" % data)
            return
        key=snac[5][2:]
        encpass=encryptPasswordMD5(self.password,key)
        self.sendFLAP(SNAC(0x17,0x02,0,
                           TLV(TLV_USERNAME,self.username)+
                           TLV(TLV_PASSWORD,encpass)+
                           TLV(0x004C, '')+ # unknown
                           TLV(TLV_CLIENTNAME,"AOL Instant Messenger (SM), version 5.1.3036/WIN32")+
                           TLV(0x0016,"\x01\x09")+
                           TLV(TLV_CLIENTMAJOR,"\000\005")+
                           TLV(TLV_CLIENTMINOR,"\000\001")+
                           TLV(0x0019,"\000\000")+
                           TLV(TLV_CLIENTSUB,"\x0B\xDC")+
                           TLV(0x0014,"\x00\x00\x00\xD2")+
                           TLV(TLV_LANG,"en")+
                           TLV(TLV_COUNTRY,"us")+
                           TLV(TLV_USESSI,"\001")))
        return "Cookie"

    def oscar_Cookie(self,data):
        snac=readSNAC(data[1])
        if not snac:
            log.msg("Illegal SNAC data received in oscar_Cookie: %s" % data)
            return
        if self.icq:
            i=snac[5].find("\000")
            snac[5]=snac[5][i:]
        tlvs=readTLVs(snac[5])
        log.msg(tlvs)
        if tlvs.has_key(6):
            self.cookie=tlvs[6]
            server,port=string.split(tlvs[5],":")
            d = self.connectToBOS(server, int(port))
            d.addErrback(lambda x: log.msg("Connection Failed! Reason: %s" % x))
            if self.deferred:
                d.chainDeferred(self.deferred)
            self.disconnect()
        elif tlvs.has_key(8):
            errorcode=tlvs[8]
            errorurl=tlvs[4]
            if errorcode=='\x00\x05':
                error="Incorrect username or password."
            elif errorcode=='\x00\x11':
                error="Your account is currently suspended."
            elif errorcode=='\x00\x14':
                error="The instant messenger server is temporarily unavailable"
            elif errorcode=='\x00\x18':
                error="You have been connecting and disconnecting too frequently. Wait ten minutes and try again. If you continue to try, you will need to wait even longer."
            elif errorcode=='\x00\x1c':
                error="The client version you are using is too old.  Please contact the maintainer of this software if you see this message so that the problem can be resolved."
            else: error=repr(errorcode)
            self.error(error,errorurl)
        else:
            log.msg('hmm, weird tlvs for %s cookie packet' % str(self))
            log.msg(tlvs)
            log.msg('snac')
            log.msg(str(snac))
        return "None"

    def oscar_None(self,data): pass

    def connectToBOS(self, server, port):
        c = protocol.ClientCreator(reactor, self.BOSClass, self.username, self.cookie)
        return c.connectTCP(server, int(port))

    def error(self,error,url):
        log.msg("ERROR! %s %s" % (error,url))
        if self.deferred: self.deferred.errback((error,url))
        self.transport.loseConnection()

FLAP_CHANNEL_NEW_CONNECTION = 0x01
FLAP_CHANNEL_DATA = 0x02
FLAP_CHANNEL_ERROR = 0x03
FLAP_CHANNEL_CLOSE_CONNECTION = 0x04

SERVICE_ADMIN = 0x07
SERVICE_CHATNAV = 0x0d
SERVICE_CHAT = 0x0e
SERVICE_DIRECTORY = 0x0f
SERVICE_SSBI = 0x10
SERVICE_EMAIL = 0x18
serviceClasses = {
    SERVICE_ADMIN:AdminService,
    SERVICE_CHATNAV:ChatNavService,
    SERVICE_CHAT:ChatService,
    SERVICE_DIRECTORY:DirectoryService,
    SERVICE_SSBI:SSBIService,
    SERVICE_EMAIL:EmailService
}
TLV_USERNAME = 0x0001
TLV_CLIENTNAME = 0x0003
TLV_COUNTRY = 0x000E
TLV_LANG = 0x000F
TLV_CLIENTMAJOR = 0x0017
TLV_CLIENTMINOR = 0x0018
TLV_CLIENTSUB = 0x001A
TLV_PASSWORD = 0x0025
TLV_USESSI = 0x004A

###
# Capabilities
###

# Supports avatars/buddy icons
CAP_ICON = '\x09\x46\x13\x46\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# User is using iChat
CAP_ICHAT = '\x09\x46\x00\x00\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
CAP_ICHATAV = '\x09\x46\x01\x05\x4C\x7F\x11\xD1\x82\x22\x44\x45\x45\x53\x54\x00'
# Supports voice chat
CAP_VOICE = '\x09\x46\x13\x41\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports direct image/direct im
CAP_IMAGE = '\x09\x46\x13\x45\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports chat
CAP_CHAT = '\x74\x8F\x24\x20\x62\x87\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports file transfers (can accept files)
CAP_GET_FILE = '\x09\x46\x13\x48\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports file transfers (can send files)
CAP_SEND_FILE = '\x09\x46\x13\x43\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports games
CAP_GAMES = '\x09\x46\x13\x4A\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports buddy list transfer
CAP_SEND_LIST = '\x09\x46\x13\x4B\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports channel 2 extended
CAP_SERV_REL = '\x09\x46\x13\x49\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Allow communication between ICQ and AIM
CAP_CROSS_CHAT = '\x09\x46\x13\x4D\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports UTF-8 encoded messages, only used with ICQ
CAP_UTF = '\x09\x46\x13\x4E\x4C\x7F\x11\xD1\x82\x22\x44\x45\x53\x54\x00\x00'
# Supports RTF messages
CAP_RTF = '\x97\xB1\x27\x51\x24\x3C\x43\x34\xAD\x22\xD6\xAB\xF7\x3F\x14\x92'

CAPS = dict( [
    (CAP_ICON, 'icon'),
    (CAP_VOICE, 'voice'),
    (CAP_IMAGE, 'image'),
    (CAP_CHAT, 'chat'),
    (CAP_GET_FILE, 'getfile'),
    (CAP_SEND_FILE, 'sendfile'),
    (CAP_SEND_LIST, 'sendlist'),
    (CAP_GAMES, 'games'),
    (CAP_SERV_REL, 'serv_rel'),
    (CAP_CROSS_CHAT, 'cross_chat'),
    (CAP_UTF, 'unicode'),
    (CAP_RTF, 'rtf'),

    # From gaim-1.3.0/src/protocols/oscar/locate.c:

    ('\x09\x46\x00\x00\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'ichat'),

    ('\x09\x46\x00\x01\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'secureim'),

    ('\x09\x46\x01\x00\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'video'),

    # "Live Video" support in Windows AIM 5.5.3501 and newer
    ('\x09\x46\x01\x01\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'live_video'),

    # "Camera" support in Windows AIM 5.5.3501 and newer
    ('\x09\x46\x01\x02\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'camera'),

    # In Windows AIM 5.5.3501 and newer
    ('\x09\x46\x01\x03\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'generecunknown'),

    # In iChatAV (version numbers...?)
    ('\x09\x46\x01\x05\x4c\x7f\x11\xd1\x82\x22\x44\x45\x45\x53\x54\x00',
     'ichatav'),

    # Not really sure about this one.  In an email from 26 Sep 2003,
    # Matthew Sachs suggested that, "this * is probably the capability
    # for the SMS features."
    ('\x09\x46\x01\xff\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'sms'),

    ('\x09\x46\xf0\x03\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'generecunknown2'),

    ('\x09\x46\xf0\x04\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'generecunknown3'),

    ('\x09\x46\xf0\x05\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'generecunknown4'),

    ('\x09\x46\x13\x23\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'hiptop'),

    ('\x09\x46\x13\x44\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'icq_direct'),

    ('\x09\x46\x13\x47\x4c\x7f\x11\xd1\x82\x22\x44\x45\x53\x54\x00\x00',
     'addins'),

    ('\x09\x46\x13\x4a\x4c\x7f\x11\xd1\x22\x82\x44\x45\x53\x54\x00\x00',
     'games2'),

    ('\x2e\x7a\x64\x75\xfa\xdf\x4d\xc8\x88\x6f\xea\x35\x95\xfd\xb6\xdf',
     'icqutf8old'),

    ('\x56\x3f\xc8\x09\x0b\x6f\x41\xbd\x9f\x79\x42\x26\x09\xdf\xa2\xf3',
     'icq2go'),

    ('\x97\xb1\x27\x51\x24\x3c\x43\x34\xad\x22\xd6\xab\xf7\x3f\x14\x09',
     'generecunknown5'),

    ('\xaa\x4a\x32\xb5\xf8\x84\x48\xc6\xa3\xd7\x8c\x50\x97\x19\xfd\x5b',
     'apinfo'),

    ('\xf2\xe7\xc7\xf4\xfe\xad\x4d\xfb\xb2\x35\x36\x79\x8b\xdf\x00\x00',
     'trilliancrypt'),

    ('\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00',
     'empty')
    ] )

###
# Status indicators
###
# Web status icons should be updated to show status
STATUS_WEBAWARE = 0x0001
# IP address should be provided to requestors
STATUS_SHOWIP = 0x0002
# Indicate that it is the user's birthday
STATUS_BIRTHDAY = 0x0008
# "User active webfront flag"... no idea
STATUS_WEBFRONT = 0x0020
# Client does not support direct connections
STATUS_DCDISABLED = 0x0100
# Client will do direct connections upon authorization
STATUS_DCAUTH = 0x1000
# Client will only do direct connections with contact users
STATUS_DCCONT = 0x2000

###
# Typing notification status codes
###
MTN_FINISH = '\x00\x00'
MTN_IDLE = '\x00\x01'
MTN_BEGIN = '\x00\x02'

# Motd types list
MOTDS = dict( [
    (0x01, "Mandatory upgrade needed notice"),
    (0x02, "Advisable upgrade notice"),
    (0x03, "AIM/ICQ service system announcements"),
    (0x04, "Standard notice"),
    (0x06, "Some news from AOL service") ] )

###
# SSI Types
###
AIM_SSI_TYPE_BUDDY = 0x0000
AIM_SSI_TYPE_GROUP = 0x0001
AIM_SSI_TYPE_PERMIT = 0x0002
AIM_SSI_TYPE_DENY = 0x0003
AIM_SSI_TYPE_PDINFO = 0x0004
AIM_SSI_TYPE_PRESENCEPREFS = 0x0005
AIM_SSI_TYPE_ICQSHORTCUT = 0x0009 # Not sure if this is true
AIM_SSI_TYPE_IGNORE = 0x000e
AIM_SSI_TYPE_LASTUPDATE = 0x000f
AIM_SSI_TYPE_SMS = 0x0010
AIM_SSI_TYPE_IMPORTTIME = 0x0013
AIM_SSI_TYPE_ICONINFO = 0x0014
