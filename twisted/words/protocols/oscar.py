# Copyright (c) 2001-2004 Twisted Matrix Laboratories.
# See LICENSE for details.

"""An implementation of the OSCAR protocol, which AIM and ICQ use to communcate.

This module is unstable.

Maintainer: U{Paul Swartz<mailto:z3p@twistedmatrix.com>}
Modifications done by: U{Daniel Henninger<mailto:jadestorm@nc.rr.com>}
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

def SNAC(fam,sub,id,data,flags=[0,0]):
    header="!HHBBL"
    head=struct.pack(header,fam,sub,
                     flags[0],flags[1],
                     id)
    return head+str(data)

def readSNAC(data):
    header="!HHBBL"
    head=list(struct.unpack(header,data[:10]))
    return head+[data[10:]]

def TLV(type,value):
    header="!HH"
    head=struct.pack(header,type,len(value))
    return head+str(value)

def readTLVs(data,count=None):
    header="!HH"
    dict={}
    while data and len(dict)!=count:
        head=struct.unpack(header,data[:4])
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
    text=string.replace(text,"<br>","\n")
    text=string.replace(text,"<BR>","\n")
    text=string.replace(text,"<Br>","\n") # XXX make this a regexp
    text=string.replace(text,"<bR>","\n")
    text=re.sub('<.*?>','',text)
    text=string.replace(text,'&gt;','>')
    text=string.replace(text,'&lt;','<')
    text=string.replace(text,'&nbsp;',' ')
    #text=string.replace(text,'&#34;','"')
    text=string.replace(text,'&amp;','&')
    text=string.replace(text,'&quot;','"')
    return text

def html(text):
    #text=string.replace(text,'"','&#34;')
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
        for k,v in tlvs.items():
            if k == 1: # user flags
                v=struct.unpack('!H',v)[0]
                for o, f in [(1,'trial'),
                             (2,'unknown bit 2'),
                             (4,'aol'),
                             (8,'unknown bit 4'),
                             (16,'aim'),
                             (32,'away'),
                             (1024,'activebuddy')]:
                    if v&o: self.flags.append(f)
            elif k == 2: # member since date
                self.memberSince = struct.unpack('!L',v)[0]
            elif k == 3: # on-since
                self.onSince = struct.unpack('!L',v)[0]
            elif k == 4: # idle time
                self.idleTime = struct.unpack('!H',v)[0]
            elif k == 5: # unknown
                pass
            elif k == 6: # icq online status
                if v[2] == '\x00':
                    self.icqStatus = 'online'
                elif v[2] == '\x01':
                    self.icqStatus = 'away'
                elif v[2] == '\x02':
                    self.icqStatus = 'dnd'
                elif v[2] == '\x04':
                    self.icqStatus = 'xa'
                elif v[2] == '\x10':
                    self.icqStatus = 'busy'
                else:
                    self.icqStatus = 'unknown'
            elif k == 10: # icq ip address
                self.icqIPaddy = socket.inet_ntoa(v)
            elif k == 12: # icq random stuff
                # from http://iserverd1.khstu.ru/oscar/info_block.html
                self.icqRandom = struct.unpack('!4sLBHLLLLLLH',v)
                self.icqLANIPaddy = socket.inet_ntoa(self.icqRandom[0])
                self.icqLANIPport = self.icqRandom[1]
                self.icqProtocolVersion = self.icqRandom[3]
            elif k == 13: # capabilities
                caps=[]
                while v:
                    c=v[:16]
                    if CAPS.has_key(c): caps.append(CAPS[c])
                    else: caps.append(("unknown",c))
                    v=v[16:]
                caps.sort()
                self.caps=caps
            elif k == 14: pass
            elif k == 15: # session length (aim)
                self.sessionLength = struct.unpack('!L',v)[0]
            elif k == 16: # session length (aol)
                self.sessionLength = struct.unpack('!L',v)[0]
            elif k == 30: # no idea
                pass
            else:
                log.msg("unknown tlv for user %s\nt: %s\nv: %s"%(self.name,k,repr(v)))

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

    def oscarRep(self):
        data = struct.pack(">H", len(self.name)) +self.name
        tlvs = TLV(0xc8, struct.pack(">H",len(self.users)))
        data += struct.pack(">4H", self.groupID, self.buddyID, 1, len(tlvs))
        return data+tlvs
#	if len(self.users) > 0:
#	        tlvData = TLV(0xc8, reduce(lambda x,y:x+y, [struct.pack('!H',self.usersToID[x]) for x in self.users]))
#	else:
#		tlvData = ""
#        return struct.pack('!H', len(self.name)) + self.name + \
#               struct.pack('!HH', groupID, buddyID) + '\000\001' + \
#               struct.pack(">H", len(tlvData)) + tlvData


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
            tlvs += TLV(0x0066, "") # awaiting authozir
        data += struct.pack(">4H", self.groupID, self.buddyID, 0, len(tlvs))
        return data+tlvs
#        tlvData = reduce(lambda x,y: x+y, map(lambda (k,v):TLV(k,v), self.tlvs.items()), '\000\000')
#        return struct.pack('!H', len(self.name)) + self.name + \
#               struct.pack('!HH', groupID, buddyID) + '\000\000' + tlvData


class OscarConnection(protocol.Protocol):
    def connectionMade(self):
        self.state=""
        self.seqnum=0
        self.buf=''
        self.outRate=6000
        self.outTime=time.time()
        self.stopKeepAliveID = None
        self.setKeepAlive(4*60) # 4 minutes

    def connectionLost(self, reason):
        log.msg("Connection Lost! %s" % self)
        self.stopKeepAlive()

#    def connectionFailed(self):
#        log.msg("Connection Failed! %s" % self)
#        self.stopKeepAlive()

    def sendFLAP(self,data,channel = 0x02):
        header="!cBHH"
	if (not hasattr(self, "seqnum")):
		self.seqnum = 0
        self.seqnum=(self.seqnum+1)%0xFFFF
        seqnum=self.seqnum
        head=struct.pack(header,'*', channel,
                         seqnum, len(data))
        self.transport.write(head+str(data))
#        if isinstance(self, ChatService):
#            logPacketData(head+str(data))

    def readFlap(self):
        if len(self.buf)<6: return
        flap=struct.unpack("!BBHH",self.buf[:6])
        if len(self.buf)<6+flap[3]: return
        data,self.buf=self.buf[6:6+flap[3]],self.buf[6+flap[3]:]
        return [flap[1],data]

    def dataReceived(self,data):
        logPacketData(data)
        self.buf=self.buf+data
        flap=self.readFlap()
        while flap:
            func=getattr(self,"oscar_%s"%self.state,None)
            if not func:
                log.msg("no func for state: %s" % self.state)
            state=func(flap)
            if state:
                self.state=state
            flap=self.readFlap()

    def setKeepAlive(self,t):
        self.keepAliveDelay=t
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
        self.supportedFamilies = ()
        self.requestCallbacks={} # request id:Deferred
        self.scheduler=Scheduler(self.sendFLAP)

    def sendSNAC(self,fam,sub,data,flags=[0,0]):
        """
        send a snac and wait for the response by returning a Deferred.
        """
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
        snac=SNAC(fam,sub,0x10000*fam+sub,data)
        self.scheduler.enqueue(fam,sub,snac)

    def oscar_(self,data):
        self.sendFLAP("\000\000\000\001"+TLV(6,self.cookie), 0x01)
        return "Data"

    def oscar_Data(self,data):
        snac=readSNAC(data[1])
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
        self.supportedFamilies = struct.unpack("!"+str(numFamilies)+'H', snac[3])
        d = ''
        for fam in self.supportedFamilies:
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
        #if (code==3):
        #       import sys
        #       sys.exit()

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
            if self.snacFamilies.has_key(fam):
                version, toolID, toolVersion = self.snacFamilies[fam]
                d = d + struct.pack('!4H',fam,version,toolID,toolVersion)
        self.sendSNACnr(0x01,0x02,d)

class BOSConnection(SNACBased):
    snacFamilies = {
        0x01:(3, 0x0110, 0x059b),
        0x13:(3, 0x0110, 0x059b),
        0x02:(1, 0x0110, 0x059b),
        0x03:(1, 0x0110, 0x059b),
        0x04:(1, 0x0110, 0x059b),
        0x06:(1, 0x0110, 0x059b),
        0x08:(1, 0x0104, 0x0001),
        0x09:(1, 0x0110, 0x059b),
        0x0a:(1, 0x0110, 0x059b),
        0x0b:(1, 0x0104, 0x0001),
        0x0c:(1, 0x0104, 0x0001)
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
        tlvs = readTLVs(snac[3][2:])
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
                if k == 2:
                    while v:
                        v = v[2:] # skip bad data
                        messageLength, charSet, charSubSet = struct.unpack('!3H', v[:6])
                        messageLength -= 4
                        message = [v[6:6+messageLength]]
                        if charSet == 0:
                            pass # don't add anything special
                        elif charSet == 2:
                            message.append('unicode')
                        elif charSet == 3:
                            message.append('iso-8859-1')
                        elif charSet == 0xffff:
                            message.append('none')
                        if charSubSet == 0xb:
                            message.append('macintosh')
                        if messageLength > 0: multiparts.append(tuple(message))
                        v = v[6+messageLength:]
                elif k == 3:
                    flags.append('acknowledge')
                elif k == 4:
                    flags.append('auto')
                elif k == 6:
                    flags.append('offline')
                elif k == 8:
                    iconLength, foo, iconSum, iconStamp = struct.unpack('!LHHL',v)
                    if iconLength:
                        flags.append('icon')
                        flags.append((iconLength, iconSum, iconStamp))
                elif k == 9:
                    flags.append('buddyrequest')
                elif k == 0xb: # unknown
                    pass
                elif k == 0x17:
                    flags.append('extradata')
                    flags.append(v)
                else:
                    log.msg('unknown TLV for incoming IM, %04x, %s' % (k,repr(v)))

#  unknown tlv for user SNewdorf
#  t: 29
#  v: '\x00\x00\x00\x05\x02\x01\xd2\x04r\x00\x01\x01\x10/\x8c\x8b\x8a\x1e\x94*\xbc\x80}\x8d\xc4;\x1dEM'
# XXX what is this?
            self.receiveMessage(user, multiparts, flags)
        elif channel == 2: # rondevouz
            status = struct.unpack('!H',tlvs[5][:2])[0]
            requestClass = tlvs[5][10:26]
            moreTLVs = readTLVs(tlvs[5][26:])
            if requestClass == CAP_CHAT: # a chat request
                exchange = struct.unpack('!H',moreTLVs[10001][:2])[0]
                name = moreTLVs[10001][3:-2]
                instance = struct.unpack('!H',moreTLVs[10001][-2:])[0]
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
                name = moreTLVs[10001][9:-7]
                desc = moreTLVs[12]
                log.msg('file request from %s, %s, %s' % (user, name, desc))
                self.receiveSendFileRequest(user, name, desc, cookie)
            else:
                log.msg('unsupported rondevouz: %s' % requestClass)
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
                        self.gotAuthorizationRespons(uin, False)
                    elif messageType == 0x08:
                        # authorization ok
                        self.gotAuthorizationRespons(uin, True)
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
        if (type == 0x01):
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
        if 0x80 & snac[0] or 0x80 & snac[1]:
            sLen,id,length = struct.unpack(">HHH", snac[3][:6])
            pos = 6 + length
        uinlen = ord(snac[3][pos])
        pos += 1
        uin = snac[3][pos:pos+uinlen]
        pos += uinlen
        self.gotAuthorizationRequest(uin)


    def oscar_13_1B(self, snac):
        """
        Got authorization respons
        """
        pos = 0
        if 0x80 & snac[0] or 0x80 & snac[1]:
            sLen,id,length = struct.unpack(">HHH", snac[3][:6])
            pos = 6 + length
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
            self.gotAuthorizationRespons(uin, True)
        else:
            # authorization request was not granted
            self.gotAuthorizationRespons(uin, False)

    def oscar_13_1C(self, snac):
        """
        SSI Your were added to someone's buddylist
        """
        pos = 0
        if 0x80 & snac[0] or 0x80 & snac[1]:
            sLen,id,length = struct.unpack(">HHH", snac[3][:6])
            pos = 6 + length
            val = snac[3][4:pos]
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

    def _cbRequestSelfInfo(self, snac, d):
        d.callback(self.parseUser(snac[5]))

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
            revision, groups, permit, deny, permitMode, visibility = args
        else:
            version, revision = struct.unpack('!BH', snac[5][:3])
            groups = {}
            permit = []
            deny = []
            permitMode = None
            visibility = None
        while len(itemdata)>4:
            nameLength = struct.unpack('!H', itemdata[:2])[0]
            name = itemdata[2:2+nameLength]
            groupID, buddyID, itemType, restLength = \
                struct.unpack('!4H', itemdata[2+nameLength:10+nameLength])
            tlvs = readTLVs(itemdata[10+nameLength:10+nameLength+restLength])
            itemdata = itemdata[10+nameLength+restLength:]
            if itemType == 0: # buddies
                groups[groupID].addUser(buddyID, SSIBuddy(name, groupID, buddyID, tlvs))
            elif itemType == 1: # group
                g = SSIGroup(name, groupID, buddyID, tlvs)
                if groups.has_key(0): groups[0].addUser(groupID, g)
                groups[groupID] = g
            elif itemType == 2: # permit
                permit.append(name)
            elif itemType == 3: # deny
                deny.append(name)
            elif itemType == 4: # permit deny info
                if not tlvs.has_key(0xcb):
                    continue # this happens with ICQ
                permitMode = {1:'permitall',2:'denyall',3:'permitsome',4:'denysome',5:'permitbuddies'}[ord(tlvs[0xca])]
                visibility = {'\xff\xff\xff\xff':'all','\x00\x00\x00\x04':'notaim'}.get(tlvs[0xcb], 'unknown')
            elif itemType == 5: # unknown (perhaps idle data)?
                pass
            else:
                log.msg('%s %s %s %s %s' % (name, groupID, buddyID, itemType, tlvs))
        timestamp = struct.unpack('!L',itemdata)[0]
        if not timestamp: # we've got more packets coming
            # which means add some deferred stuff
            d = defer.Deferred()
            self.requestCallbacks[snac[4]] = d
            d.addCallback(self._cbRequestSSI, (revision, groups, permit, deny, permitMode, visibility))
            d.addErrback(self._ebDeferredRequestSSIError, revision, groups, permit, deny, permitMode, visibility)
            return d
        if (len(groups) <= 0):
		gusers = None
	else:
		gusers = groups[0].users
        return (gusers,permit,deny,permitMode,visibility,timestamp,revision)

    def _ebDeferredRequestSSIError(self, error, revision, groups, permit, deny, permitMode, visibility):
        log.msg('ERROR IN REQUEST SSI DEFERRED %s' % error)

    def activateSSI(self):
        """
        active the data stored on the server (use buddy list, permit deny settings, etc.)
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
        if snac[2] & 0x80 or snac[3] & 0x80:
            sLen,id,length = struct.unpack(">HHH", snac[5][:6])
            pos = 6 + length
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
            if isinstance(item, SSIGroup):
                groupID = 0
            else:
                groupID = item.group.group.findIDFor(item.group)
        if buddyID is None:
            if hasattr(item, "group"):
                buddyID = item.group.findIDFor(item)
            else:
                buddyID = 0
        return self.sendSNAC(0x13,0x09, item.oscarRep())

    def delItemSSI(self, item):
        return self.sendSNAC(0x13,0x0A, item.oscarRep())

    def endModifySSI(self):
        self.sendSNACnr(0x13,0x12,'')

    def setProfile(self, profile):
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

    def sendAuthorizationRespons(self, uin, success, responsString):
        """
        send an authorization respons
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
        d.arm()
        self.oscar_01_05(snac[2:], d)

    def createChat(self, shortName):
        """
        create a chat room
        """
        if self.services.has_key(SERVICE_CHATNAV):
            return self.services[SERVICE_CHATNAV].createChat(shortName)
        else:
            d = defer.Deferred()
            d.addErrback(self._ebDeferredCreateChatError)
            self.connectService(SERVICE_CHATNAV,1).addCallback(lambda s:d.arm() or s.createChat(shortName).chainDeferred(d))
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
#	return [nick,first,last,email]

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

    def gotAuthorizationRespons(self, uin, success):
        """
        called when a user sends an authorization respons
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

    def receiveSendFileRequest(self, user, file, description, cookie):
        """
        called when someone tries to send a file to us
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
        0x01:(3, 0x0010, 0x059b),
        0x0d:(1, 0x0010, 0x059b)
    }

    def oscar_01_07(self, snac):
        # rate info
        self.sendSNACnr(0x01, 0x08, '\000\001\000\002\000\003\000\004\000\005')
        self.sendSNACnr(0x0d, 0x02, '')

    def oscar_0D_09(self, snac):
        self.clientReady()

    def getChatInfo(self, exchange, name, instance):
        d = defer.Deferred()
        d.addErrback(self._ebDeferredRequestSSIError)
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

    def createChat(self, shortName):
        #d = defer.Deferred()
        data = '\x00\x04\x06create\xff\xff\x01\x00\x03'
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
        0x01:(3, 0x0010, 0x059b),
        0x0E:(1, 0x0010, 0x059b)
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
        tlvs=TLV(0x02,"us-ascii")+TLV(0x03,"en")+TLV(0x01,message)
        self.sendSNAC(0x0e,0x05,
                      "\x46\x30\x38\x30\x44\x00\x63\x00\x00\x03\x00\x01\x00\x00\x00\x06\x00\x00\x00\x05"+
                      struct.pack("!H",len(tlvs))+
                      tlvs)

    def leaveChat(self):
        self.disconnect()

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
        key=snac[5][2:]
        encpass=encryptPasswordMD5(self.password,key)
        self.sendFLAP(SNAC(0x17,0x02,0,
                           TLV(TLV_USERNAME,self.username)+
                           TLV(TLV_PASSWORD,encpass)+
                           TLV(0x004C, '')+ # unknown
                           TLV(TLV_CLIENTNAME,"AOL Instant Messenger (SM), version 4.8.2790/WIN32")+
                           TLV(0x0016,"\x01\x09")+
                           TLV(TLV_CLIENTMAJOR,"\000\004")+
                           TLV(TLV_CLIENTMINOR,"\000\010")+
                           TLV(0x0019,"\000\000")+
                           TLV(TLV_CLIENTSUB,"\x0A\xE6")+
                           TLV(0x0014,"\x00\x00\x00\xBB")+
                           TLV(TLV_LANG,"en")+
                           TLV(TLV_COUNTRY,"us")+
                           TLV(TLV_USESSI,"\001")))
        return "Cookie"

    def oscar_Cookie(self,data):
        snac=readSNAC(data[1])
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
            if errorcode=='\000\030':
                error="You are attempting to sign on again too soon.  Please try again later."
            elif errorcode=='\000\005':
                error="Invalid Username or Password."
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

SERVICE_CHATNAV = 0x0d
SERVICE_CHAT = 0x0e
serviceClasses = {
    SERVICE_CHATNAV:ChatNavService,
    SERVICE_CHAT:ChatService
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
# Supports UTF-8 encoded messages
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
    (0x04, "Standart notice"),
    (0x06, "Some news from AOL service") ] )
