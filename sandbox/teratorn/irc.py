# -*- test-case-name: twisted.test.test_irc -*-
#
# Copyright (c) 2001-2004 Twisted Matrix Laboratories.
# See LICENSE for details.


"""Internet Relay Chat Protocol for client and server.

Stability: semi-stable.

Future Plans
============

The way the IRCClient class works here encourages people to implement
IRC clients by subclassing the ephemeral protocol class, and it tends
to end up with way more state than it should for an object which will
be destroyed as soon as the TCP transport drops.  Someone oughta do
something about that, ya know?

The DCC support needs to have more hooks for the client for it to be
able to ask the user things like \"Do you want to accept this session?\"
and \"Transfer #2 is 67% done.\" and otherwise manage the DCC sessions.

Test coverage needs to be better.

@author: U{Kevin Turner<mailto:acapnotic@twistedmatrix.com>}

@see: RFC 1459: Internet Relay Chat Protocol
@see: RFC 2812: Internet Relay Chat: Client Protocol
@see: U{The Client-To-Client-Protocol
<http://www.irchelp.org/irchelp/rfc/ctcpspec.html>}
"""

__version__ = '$Revision: 1.7 $'[11:-2]

from twisted.internet import reactor, protocol, defer
from twisted.persisted import styles
from twisted.protocols import basic
from twisted.python import log, reflect, text

# System Imports

import errno
import os
import random
import re
import stat
import string
import struct
import sys
import time
import types
import traceback
import socket

from os import path

NUL = chr(0)
CR = chr(015)
NL = chr(012)
LF = NL
SPC = chr(040)

CHANNEL_PREFIXES = '&#!+'

class IRCBadMessage(Exception):
    pass

class IRCPasswordMismatch(Exception):
    pass

def parsemsg(s):
    """Breaks a message from an IRC server into its prefix, command, and arguments.
    """
    prefix = ''
    trailing = []
    if not s:
        raise IRCBadMessage("Empty line.")
    if s[0] == ':':
        prefix, s = string.split(s[1:], ' ', 1)
    if string.find(s,' :') != -1:
        s, trailing = string.split(s, ' :', 1)
        args = string.split(s)
        args.append(trailing)
    else:
        args = string.split(s)
    command = args.pop(0)
    return prefix, command, args


def split(str, length = 80):
    """I break a message into multiple lines.

    I prefer to break at whitespace near str[length].  I also break at \\n.

    @returns: list of strings
    """
    r = []
    while len(str) > length:
        w, n = str[:length].rfind(' '), str[:length].find('\n')
        if w == -1 and n == -1:
            line, str = str[:length], str[length:]
        else:
            i = n == -1 and w or n
            line, str = str[:i], str[i+1:]
        r.append(line)
    if len(str):
        r.extend(str.split('\n'))
    return r

class IRC(protocol.Protocol):
    """Internet Relay Chat server protocol.
    """

    buffer = ""
    hostname = None

    def connectionMade(self):
        log.msg("irc connection made")
        self.channels = []
        if self.hostname is None:
            self.hostname = socket.getfqdn()

    def sendLine(self, line):
        log.msg('send: %s' % line)
        self.transport.write("%s%s%s" % (line, CR, LF))

    def sendMessage(self, command, *parameter_list, **prefix):
        """Send a line formatted as an IRC message.

        First argument is the command, all subsequent arguments
        are parameters to that command.  If a prefix is desired,
        it may be specified with the keyword argument 'prefix'.
        """

        if not command:
            raise ValueError, "IRC message requires a command."

        if ' ' in command or command[0] == ':':
            # Not the ONLY way to screw up, but provides a little
            # sanity checking to catch likely dumb mistakes.
            raise ValueError, "Somebody screwed up, 'cuz this doesn't" \
                  " look like a command to me: %s" % command

        line = string.join([command] + list(parameter_list))
        if prefix.has_key('prefix'):
            line = ":%s %s" % (prefix['prefix'], line)
        self.sendLine(line)

        if len(parameter_list) > 15:
            log.msg("Message has %d parameters (RFC allows 15):\n%s" %
                    (len(parameter_list), line))

    def dataReceived(self, data):
        """This hack is to support mIRC, which sends LF only,
        even though the RFC says CRLF.  (Also, the flexibility
        of LineReceiver to turn "line mode" on and off was not
        required.)
        """
        self.buffer = self.buffer + data
        lines = string.split(self.buffer, LF)
        # Put the (possibly empty) element after the last LF back in the
        # buffer
        self.buffer = lines.pop()

        for line in lines:
            if len(line) <= 2:
                # This is a blank line, at best.
                continue
            if line[-1] == CR:
                line = line[:-1]
            prefix, command, params = parsemsg(line)
            # mIRC is a big pile of doo-doo
            command = string.upper(command)
            # DEBUG: log.msg( "%s %s %s" % (prefix, command, params))

            self.handleCommand(command, prefix, params)


    def handleCommand(self, command, prefix, params):
        """Determine the function to call for the given command and call
        it with the given arguments.
        """
        method = getattr(self, "irc_%s" % command, None)
        try:
            if method is not None:
                method(prefix, params)
            else:
                self.irc_unknown(prefix, command, params)
        except:
            log.deferr()


    def irc_unknown(self, prefix, command, params):
        """Implement me!"""
        raise NotImplementedError
    
    # Helper methods
    def privmsg(self, sender, recip, message):
        """Send a message to a channel or user
        
        @type sender: C{str}
        @param sender: Who is sending this message.  Should be of the form
        username!ident@hostmask (unless you know better!).
        
        @type recip: C{str}
        @param recip: The recipient of this message.  If a channel, it
        must start with a channel prefix.
        
        @type message: C{str}
        @param message: The message being sent.
        """
        self.sendLine(":%s PRIVMSG %s :%s" % (sender, recip, message))
    
    def notice(self, sender, recip, message):
        """Send a \"notice\" to a channel or user.
        
        Notices differ from privmsgs in that the RFC claims they are different.
        Robots are supposed to send notices and not respond to them.  Clients
        typically display notices differently from privmsgs.
        
        @type sender: C{str}
        @param sender: Who is sending this message.  Should be of the form
        username!ident@hostmask (unless you know better!).
        
        @type recip: C{str}
        @param recip: The recipient of this message.  If a channel, it
        must start with a channel prefix.
        
        @type message: C{str}
        @param message: The message being sent.
        """
        self.sendLine(":%s NOTICE %s :%s" % (sender, recip, message))

    def action(self, sender, recip, message):
        """Send an action to a channel or user.
        
        @type sender: C{str}
        @param sender: Who is sending this message.  Should be of the form
        username!ident@hostmask (unless you know better!).
        
        @type recip: C{str}
        @param recip: The recipient of this message.  If a channel, it
        must start with a channel prefix.
        
        @type message: C{str}
        @param message: The action being sent.
        """
        self.sendLine(":%s ACTION %s :%s" % (sender, recip, message))

    def topic(self, user, channel, topic, author=None):
        """Send the topic to a user.
        
        @type user: C{str}
        @param user: The user receiving the topic.  Only their nick name, not
        the full hostmask.
        
        @type channel: C{str}
        @param channel: The channel for which this is the topic.
        
        @type topic: C{str}
        @param topic: The topic string.
        
        @type author: C{str}
        @param author: If the topic is being changed, the full username and hostmask
        of the person changing it.
        """
        if author is None:
            self.sendLine(":%s %s %s %s :%s" % (
                self.hostname, RPL_TOPIC, user, channel, topic))
        else:
            self.sendLine(":%s TOPIC %s :%s" % (author, channel, topic))

    def names(self, user, channel, names):
        """Send the names of a channel's participants to a user.
        
        @type user: C{str}
        @param user: The user receiving the topic.  Only their nick name, not
        the full hostmask.
        
        @type channel: C{str}
        @param channel: The channel for which this is the topic.
        
        @type names: C{list} of C{str}
        @param names: The names to send.
        """
        self.sendLine(":%s %s %s = %s :%s" % (
            self.hostname, RPL_NAMREPLY, user, channel, ' '.join(names)))
        self.sendLine(":%s %s %s %s :End of /NAMES list" % (
            self.hostname, RPL_ENDOFNAMES, user, channel))

    def join(self, who, where):
        """Send a join message.
        
        @type who: C{str}
        @param who: The name of the user joining.  Should be of the form
        username!ident@hostmask (unless you know better!).
        
        @type where: C{str}
        @param where: The channel the user is joining.
        """
        self.sendLine(":%s JOIN %s" % (who, where))
    
    def part(self, who, where):
        """Send a part message.

        @type who: C{str}
        @param who: The name of the user joining.  Should be of the form
        username!ident@hostmask (unless you know better!).
        
        @type where: C{str}
        @param where: The channel the user is joining.
        """
        self.sendLine(":%s PART %s" % (who, where))


class DccFileWriter(protocol.Protocol, styles.Ephemeral):
    """A protocol to receive an incoming DCC file transfer."""
    def __init__(self, factory):
        self.factory = factory
        self.file_obj = factory.file_obj
        self.deferred = factory.deferred
        self.bytesReceived = factory.resumePos
        self.proposedSize = factory.proposedSize
        self._mode = factory._mode 

    def dataReceived(self, data):
        self.bytesReceived += len(data)
        if not self._mode == 'turbo':
            self.transport.write(struct.pack('!i', self.bytesReceived)) #acknowledge

        try:
            self.file_obj.write(data)
        except: # abort transfer
            self.transport.loseConnection()

    def connectionLost(self, reason):
        self.file_obj.flush()
        self.file_obj.close()
        if self.bytesReceived == self.proposedSize:
            self.deferred.callback(self.factory)
        else:
            self.deferred.errback(reason)


class IncomingDccFile(protocol.ClientFactory):
    """An incoming DCC file offer.

    The L{IRCClient.gotIncomingFile} method will receive an instance of this class for each DCC file offer we receive.
    .
    You should store and manage this instance outside of the originating IRCClient. Once they are established, DCC sessions may operate independently of the IRC protocol. Thus we shouldn't be forced to keep stale IRCClient's around because they contain information about active DCC sessions."""
    protocol = DccFileWriter
    accepted = False
    resume_overwrite = False
    deferred = None
    file_obj = None
    resumePos = 0 # default - change later if resuming.
     
    def __init__(self, ircClient, user, address, port, default_filename, size, mode):
        self._ircClient = ircClient
        self.user = user
        self.address = address
        self.port = port
        self.default_filename = default_filename
        self.proposedSize = size
        self._mode = mode

        self.deferred = defer.Deferred()

    def accept(self, destfile, resume_overwrite=False):
        """
        Call this to retreive the incoming dcc file.
        
        @param destfile: A file path to open and use, or a file-like-object that data will be written to. 
        @type destfile: C{str} or file-like-object.
        @param resume_overwrite: An optional parameter. Specifies whether to resume, overwrite, or do neither (default). 
        @type resume_overwrite: \"resume\", \"overwrite\", or C{False}.

        @return: L{Deferred} instance. It will callback when the file is saved, or errback if something bad happened along the way (including if the file sizes mismatch).

        @raise IOError: If destfile is a path and opening it failed.
        @raise DccFileExists: If destfile is a path, the path exists, and resume_overwrite is False.
        """
        if self.accepted:
            raise "accept() already called successfully!"

        if hasattr(destfile, 'write'): #assume it's a file-obj
            self.file_obj = destfile
        elif type(destfile) == types.StringType: #assume it's a path
            # sanity check so we don't blow away files by accident
            if path.exists(destfile):
                if not resume_overwrite: # it's there, but we can't resume or overwrite
                    raise DccFileExists()

            # now we need to open the destination file

            # we open it differently if we are resuming
            if resume_overwrite == 'resume': # yes - open for appending
                self.file_obj = file(destfile, 'a+b')
            else: # no - open for writing (and possibly truncate)
                self.file_obj = file(destfile, 'wb')
        else:
            raise 'destfile must be a string, or a file-like-object'
 
        # we now have a file-obj to work with
                
        # do we need to resume first?
        if resume_overwrite == 'resume': # yes - send the request
            self.resumePos = fileSize(self.file_obj)
            self.ircClient.ctcpMakeQuery(self.user.split('!', 1)[0], [
                ('DCC', ['RESUME', self.default_filename, str(self.port), str(self.resumePos)])])
        else: # no, we aren't resuming - we can connect right now
            self._makeConnection()

        self.accepted = True
        return self.deferred

    def reject(self):
        """Reject this transfer before it has begun."""
        if self.accepted:
            raise "Can't call reject() after accept() was called successfully!"

        self.deferred.errback(None)

    def abort(self):
        """Abort after we've called accept() successfully."""
        if not self.accepted:
            raise "Can't call abort() unless you've already called accept() successfully!"
        
        self.protocol_instance.transport.loseConnection(connDone=DccAborted())

    def _resumeRequestAccepted(self): # have to get this before we connect
        self._makeConnection()        # a transfer where we asked to resume
   
    def _makeConnection(self):
        self._ircClient._incomingDccFiles.remove(self)
        # at this point, we don't need a reference to the IRCClient any more
        del self._ircClient
        reactor.connectTCP(self.address, self.port, self)
        
    def buildProtocol(self, addr):
        self.protocol_instance = self.protocol(self)
        return self.protocol_instance


class DccFileReader(protocol.Protocol, styles.Ephemeral):
    """A protocol for sending a file over DCC"""
    def connectionMade(self):
        self.factory.listeningPort.stopListening()
        d = basic.FileSender().beginFileTransfer(self.factory.file_obj, self.transport)
        d.addBoth(self._cbFileSenderDone)
        d.chainDeferred(self.factory.deferred)
        
    def dataReceived(self, data):
        print 'dataReceived:', repr(data)

    def _cbFileSenderDone(self, arg):
        self.transport.loseConnection()
        return arg


class OutgoingDccFile(protocol.Factory):
    """An outgoing DCC file offer - don't use this class directly - use L{IRCClient.sendFile} instead.

    When you call sendFile() an instance of this class will be returned to you. These instances contain a 'deferred' attribute which will callback once the file is successfully sent, or errback if something bad happened along the way.
    
    You should store and manage this instance outside of the originating IRCClient. Once they are established, DCC sessions may operate independently of the IRC protocol. Thus we shouldn't be forced to keep stale IRCClient's around because they contain information about active DCC sessions."""
    protocol = DccFileReader
    def __init__(self, file_obj, user, ircClient, mode=None, resumable=True):
        # TODO: resumable
        self.file_obj = file_obj
        self.user = user
        self._ircClient = ircClient
        self.mode = mode
        self.resumable = resumable

        self.deferred = defer.Deferred()
        self.resumePos = False
        self.listeningPort = reactor.listenTCP(0, self)
        sock_info = self.listeningPort.getHost()

        name = file_obj.name.split(path.sep)[-1]
        dottedquad = ircClient.transport.getHost()[1]
        # dotted-quad -> long integer
        addr = str(struct.unpack("!I", "".join(map(lambda x:chr(int(x)), dottedquad.split('.'))))[0])
        port = str(sock_info[2])
        size = str(fileSize(file_obj))

        self._ircClient.ctcpMakeQuery(self.user.split('!', 1)[0], [
            ('DCC', ['SEND', name, addr, port, size])])

    def _gotResumeRequest(self, filename, resumePos):
        if not self.resumable:
            return
        # passing the filename here is only useful so we may respond
        # with the same filename. Apparently clients such as mirc will
        # send a dummy filename that may not match what we sent out.
        port = self.listeningPort.getHost()[2]
        self._ircClient.ctcpMakeQuery(self.user.split('!', 1)[0], [
            ('DCC', ['ACCEPT', filename, str(port), str(resumePos)])])
        self.resumePos = resumePos

    def buildProtocol(self, addr):
        self._ircClient._outgoingDccFiles.remove(self)
        # we don't need our reference to the IRCClient any more
        del self._ircClient
        self.protocol_instance = self.protocol()
        self.protocol_instance.factory = self
        return self.protocol_instance

 
class DccFileExists(Exception):
    def __str__(self):
        return "Destination file already exists, and we were told not to overwrite or resume."

class DccAborted(Exception):
    def __str__(self):
        return "abort() was called on this IncomingDccFile instance."


class IRCClient(basic.LineReceiver):
    """Internet Relay Chat client protocol, with sprinkles.

    In addition to providing an interface for an IRC client protocol,
    this class also contains reasonable implementations of many common
    CTCP methods.

    TODO
    ====
     - Limit the length of messages sent (because the IRC server probably
       does).
     - Add flood protection/rate limiting for my CTCP replies.
     - NickServ cooperation.  (a mix-in?)
     - Heartbeat.  The transport may die in such a way that it does not realize
       it is dead until it is written to.  Sending something (like \"PING
       this.irc-host.net\") during idle peroids would alleviate that.  If
       you're concerned with the stability of the host as well as that of the
       transport, you might care to watch for the corresponding PONG.

    @ivar nickname: Nickname the client will use.
    @ivar password: Password used to log on to the server.  May be C{None}.
    @ivar realname: Supplied to the server during login as the \"Real name\"
        or \"ircname\".

    @ivar userinfo: Sent in reply to a X{USERINFO} CTCP query.  If C{None}, no
        USERINFO reply will be sent.
        \"This is used to transmit a string which is settable by
        the user (and never should be set by the client).\"
    @ivar fingerReply: Sent in reply to a X{FINGER} CTCP query.  If C{None}, no
        FINGER reply will be sent.
    @type fingerReply: Callable or String

    @ivar versionName: CTCP VERSION reply, client name.  If C{None}, no VERSION
        reply will be sent.
    @ivar versionNum: CTCP VERSION reply, client version,
    @ivar versionEnv: CTCP VERSION reply, environment the client is running in.

    @ivar sourceURL: CTCP SOURCE reply, a URL where the source code of this
        client may be found.  If C{None}, no SOURCE reply will be sent.

    @ivar lineRate: Minimum delay between lines sent to the server.  If
        C{None}, no delay will be imposed.
    @type lineRate: Number of Seconds.
    """

    motd = ""
    nickname = 'irc'
    password = None
    realname = None
    ### Responses to various CTCP queries.

    userinfo = None
    # fingerReply is a callable returning a string, or a str()able object.
    fingerReply = None
    versionName = None
    versionNum = None
    versionEnv = None

    sourceURL = "http://twistedmatrix.com/downloads/"

    # If this is false, no attempt will be made to identify
    # ourself to the server.
    performLogin = 1

    lineRate = None
    _queue = None
    _queueEmptying = None

    delimiter = '\n' # '\r\n' will also work (see dataReceived)

    incomingDccFileClass = IncomingDccFile
    outgoingDccFileClass = OutgoingDccFile

    _incomingDccFiles = []
    _outgoingDccFiles = []

    __pychecker__ = 'unusednames=params,prefix,channel'
        
    def sendLine(self, line):
        if self.lineRate is None:
            basic.LineReceiver.sendLine(self, lowQuote(line) + '\r')
        else:
            self._queue.append(line)
            if not self._queueEmptying:
                self._queueEmptying = reactor.callLater(self.lineRate,
                                                        self._sendLine)

    def _sendLine(self):
        if self._queue:
            basic.LineReceiver.sendLine(self, lowQuote(self._queue.pop(0)) + '\r')
            self._queueEmptying = reactor.callLater(self.lineRate,
                                                    self._sendLine)
        else:
            self._queueEmptying = None


    ### Interface level client->user output methods
    ###
    ### You'll want to override these.

    ### Methods relating to the server itself
    
    def created(self, when):
        """Called with creation date information about the server, usually at logon.
        
        @type when: C{str}
        @param when: A string describing when the server was created, probably.
        """
    
    def yourHost(self, info):
        """Called with daemon information about the server, usually at logon.
        
        @type info: C{str}
        @param when: A string describing what software the server is running, probably.
        """
    
    def myInfo(self, servername, version, umodes, cmodes):
        """Called with information about the server, usually at logon.
        
        @type servername: C{str}
        @param servername: The hostname of this server.
        
        @type version: C{str}
        @param version: A description of what software this server runs.
        
        @type umodes: C{str}
        @param umodes: All the available user modes.
        
        @type cmodes: C{str}
        @param cmodes: All the available channel modes.
        """
    
    def luserClient(self, info):
        """Called with information about the number of connections, usually at logon.
        
        @type info: C{str}
        @param info: A description of the number of clients and servers
        connected to the network, probably.
        """
    
    def bounce(self, info):
        """Called with information about where the client should reconnect.
        
        @type info: C{str}
        @param info: A plaintext description of the address that should be
        connected to.
        """
    
    def isupport(self, options):
        """Called with various information about what the server supports.
        
        @type options: C{list} of C{str}
        @param options: Descriptions of features or limits of the server, possibly
        in the form "NAME=VALUE".
        """

    def luserChannels(self, channels):
        """Called with the number of channels existant on the server.
        
        @type channels: C{int}
        """

    def luserOp(self, ops):
        """Called with the number of ops logged on to the server.
        
        @type ops: C{int}
        """

    def luserMe(self, info):
        """Called with information about the server connected to.
        
        @type info: C{str}
        @param info: A plaintext string describing the number of users and servers
        connected to this server.
        """

    ### Methods involving me directly

    def privmsg(self, user, channel, message):
        """Called when I have a message from a user to me or a channel.
        """
        pass

    def joined(self, channel):
        """Called when I finish joining a channel.

        channel has the starting character (# or &) intact.
        """
        pass

    def left(self, channel):
        """Called when I have left a channel.

        channel has the starting character (# or &) intact.
        """
        pass

    def noticed(self, user, channel, message):
        """Called when I have a notice from a user to me or a channel.

        By default, this is equivalent to IRCClient.privmsg, but if your
        client makes any automated replies, you must override this!
        From the RFC::

            The difference between NOTICE and PRIVMSG is that
            automatic replies MUST NEVER be sent in response to a
            NOTICE message. [...] The object of this rule is to avoid
            loops between clients automatically sending something in
            response to something it received.
        """
        self.privmsg(user, channel, message)

    def modeChanged(self, user, channel, set, modes, args):
        """Called when a channel's modes are changed

        @type user: C{str}
        @param user: The user and hostmask which instigated this change.

        @type channel: C{str}
        @param channel: The channel for which the modes are changing.

        @type set: C{bool} or C{int}
        @param set: true if the mode is being added, false if it is being
        removed.

        @type modes: C{str}
        @param modes: The mode or modes which are being changed.

        @type args: C{tuple}
        @param args: Any additional information required for the mode
        change.
        """

    def pong(self, user, secs):
        """Called with the results of a CTCP PING query.
        """
        pass

    def signedOn(self):
        """Called after sucessfully signing on to the server.
        """
        pass

    def kickedFrom(self, channel, kicker, message):
        """Called when I am kicked from a channel.
        """
        pass

    def nickChanged(self, nick):
        """Called when my nick has been changed.
        """
        self.nickname = nick


    ### Things I observe other people doing in a channel.

    def userJoined(self, user, channel):
        """Called when I see another user joining a channel.
        """
        pass

    def userLeft(self, user, channel):
        """Called when I see another user leaving a channel.
        """
        pass

    def userKicked(self, kickee, channel, kicker, message):
        """Called when I observe someone else being kicked from a channel.
        """
        pass

    def action(self, user, channel, data):
        """Called when I see a user perform an ACTION on a channel.
        """
        pass

    def topicUpdated(self, user, channel, newTopic):
        """In channel, user changed the topic to newTopic.

        Also called when first joining a channel.
        """
        pass

    def userRenamed(self, oldname, newname):
        """A user changed their name from oldname to newname.
        """
        pass

    ### Information from the server.

    def receivedMOTD(self, motd):
        """I received a message-of-the-day banner from the server.

        motd is a list of strings, where each string was sent as a seperate
        message from the server. To display, you might want to use::

            string.join(motd, '\\n')

        to get a nicely formatted string.
        """
        pass

    ### user input commands, client->server
    ### Your client will want to invoke these.

    def join(self, channel, key=None):
        if channel[0] not in '&#!+': channel = '#' + channel
        if key:
            self.sendLine("JOIN %s %s" % (channel, key))
        else:
            self.sendLine("JOIN %s" % (channel,))

    def leave(self, channel, reason=None):
        if channel[0] not in '&#!+': channel = '#' + channel
        if reason:
            self.sendLine("PART %s :%s" % (channel, reason))
        else:
            self.sendLine("PART %s" % (channel,))

    def kick(self, channel, user, reason=None):
        if channel[0] not in '&#!+': channel = '#' + channel
        if reason:
            self.sendLine("KICK %s %s :%s" % (channel, user, reason))
        else:
            self.sendLine("KICK %s %s" % (channel, user))

    part = leave

    def topic(self, channel, topic=None):
        """Attempt to set the topic of the given channel, or ask what it is.

        If topic is None, then I sent a topic query instead of trying to set
        the topic. The server should respond with a TOPIC message containing
        the current topic of the given channel.
        """
        # << TOPIC #xtestx :fff
        if channel[0] not in '&#!+': channel = '#' + channel
        if topic != None:
            self.sendLine("TOPIC %s :%s" % (channel, topic))
        else:
            self.sendLine("TOPIC %s" % (channel,))

    def mode(self, chan, set, modes, limit = None, user = None, mask = None):
        """Change the modes on a user or channel."""
        line = 'MODE %s %s%s' % (chan, set and '+' or '-', modes)
        if limit is not None:
            line = '%s %d' % (line, limit)
        elif user is not None:
            line = '%s %s' % (line, user)
        elif mask is not None:
            line = '%s %s' % (line, mask)
        self.sendLine(line)


    def say(self, channel, message, length = None):
        if channel[0] not in '&#!+': channel = '#' + channel
        self.msg(channel, message, length)

    def msg(self, user, message, length = None):
        """Send a message to a user or channel.

        @type user: C{str}
        @param user: The username or channel name to which to direct the
        message.

        @type message: C{str}
        @param message: The text to send

        @type length: C{int}
        @param length: The maximum number of octets to send at a time.  This
        has the effect of turning a single call to msg() into multiple
        commands to the server.  This is useful when long messages may be
        sent that would otherwise cause the server to kick us off or silently
        truncate the text we are sending.  If None is passed, the entire
        message is always send in one command.
        """

        fmt = "PRIVMSG %s :%%s" % (user,)

        if length is None:
            self.sendLine(fmt % (message,))
        else:
            lines = split(message, length - len(fmt) - 2)
            map(lambda line, self=self, fmt=fmt: self.sendLine(fmt % line),
                lines)

    def notice(self, user, message):
        self.sendLine("NOTICE %s :%s" % (user, message))

    def away(self, message=''):
        self.sendLine("AWAY :%s" % message)

    def register(self, nickname, hostname='foo', servername='bar'):
        if self.password is not None:
            self.sendLine("PASS %s" % self.password)
        self.setNick(nickname)
        self.sendLine("USER %s foo bar :%s" % (nickname, self.realname))

    def setNick(self, nickname):
        self.nickname = nickname
        self.sendLine("NICK %s" % nickname)

    def quit(self, message = ''):
        self.sendLine("QUIT :%s" % message)

    ### user input commands, client->client

    def me(self, channel, action):
        """Strike a pose.
        """
        if channel[0] not in '&#!+': channel = '#' + channel
        self.ctcpMakeQuery(channel, [('ACTION', action)])

    _pings = None
    _MAX_PINGRING = 12

    def ping(self, user, text = None):
        """Measure round-trip delay to another IRC client.
        """
        if self._pings is None:
            self._pings = {}

        if text is None:
            chars = string.letters + string.digits + string.punctuation
            key = ''.join([random.choice(chars) for i in range(12)])
        else:
            key = str(text)
        self._pings[(user, key)] = time.time()
        self.ctcpMakeQuery(user, [('PING', key)])

        if len(self._pings) > self._MAX_PINGRING:
            # Remove some of the oldest entries.
            byValue = [(v, k) for (k, v) in self._pings.items()]
            byValue.sort()
            excess = self._MAX_PINGRING - len(self._pings)
            for i in xrange(excess):
                del self._pings[byValue[i][1]]

    ### server->client messages
    ### You might want to fiddle with these,
    ### but it is safe to leave them alone.

    def irc_ERR_NICKNAMEINUSE(self, prefix, params):
        self.register(self.nickname+'_')

    def irc_ERR_PASSWDMISMATCH(self, prefix, params):
        raise IRCPasswordMismatch("Password Incorrect.")

    def irc_RPL_WELCOME(self, prefix, params):
        self.signedOn()

    def irc_RPL_WHOISUSER(self, prefix, params):
        print prefix, params

    def irc_JOIN(self, prefix, params):
        nick = string.split(prefix,'!')[0]
        channel = params[-1]
        if nick == self.nickname:
            self.joined(channel)
        else:
            self.userJoined(nick, channel)

    def irc_PART(self, prefix, params):
        nick = string.split(prefix,'!')[0]
        channel = params[0]
        if nick == self.nickname:
            self.left(channel)
        else:
            self.userLeft(nick, channel)

    def irc_MODE(self, prefix, params):
        channel, rest = params[0], params[1:]
        set = rest[0][0] == '+'
        modes = rest[0][1:]
        args = rest[1:]
        self.modeChanged(prefix, channel, set, modes, tuple(args))

    def irc_PING(self, prefix, params):
        self.sendLine("PONG %s" % params[-1])

    def irc_PRIVMSG(self, prefix, params):
        user = prefix
        channel = params[0]
        message = params[-1]

        if not message: return # don't raise an exception if some idiot sends us a blank message

        if message[0]==X_DELIM:
            m = ctcpExtract(message)
            if m['extended']:
                self.ctcpQuery(user, channel, m['extended'])

            if not m['normal']:
                return

            message = string.join(m['normal'], ' ')

        self.privmsg(user, channel, message)

    def irc_NOTICE(self, prefix, params):
        user = prefix
        channel = params[0]
        message = params[-1]

        if message[0]==X_DELIM:
            m = ctcpExtract(message)
            if m['extended']:
                self.ctcpReply(user, channel, m['extended'])

            if not m['normal']:
                return

            message = string.join(m['normal'], ' ')

        self.noticed(user, channel, message)

    def irc_NICK(self, prefix, params):
        nick = string.split(prefix,'!', 1)[0]
        if nick == self.nickname:
            self.nickChanged(params[0])
        else:
            self.userRenamed(nick, params[0])

    def irc_KICK(self, prefix, params):
        """Kicked?  Who?  Not me, I hope.
        """
        kicker = string.split(prefix,'!')[0]
        channel = params[0]
        kicked = params[1]
        message = params[-1]
        if string.lower(kicked) == string.lower(self.nickname):
            # Yikes!
            self.kickedFrom(channel, kicker, message)
        else:
            self.userKicked(kicked, channel, kicker, message)

    def irc_TOPIC(self, prefix, params):
        """Someone in the channel set the topic.
        """
        user = string.split(prefix, '!')[0]
        channel = params[0]
        newtopic = params[1]
        self.topicUpdated(user, channel, newtopic)

    def irc_RPL_TOPIC(self, prefix, params):
        """I just joined the channel, and the server is telling me the current topic.
        """
        user = string.split(prefix, '!')[0]
        channel = params[1]
        newtopic = params[2]
        self.topicUpdated(user, channel, newtopic)

    def irc_RPL_NOTOPIC(self, prefix, params):
        user = string.split(prefix, '!')[0]
        channel = params[1]
        newtopic = ""
        self.topicUpdated(user, channel, newtopic)

    def irc_RPL_MOTDSTART(self, prefix, params):
        self.motd = [params[-1]]

    def irc_RPL_MOTD(self, prefix, params):
        self.motd.append(params[-1])

    def irc_RPL_ENDOFMOTD(self, prefix, params):
        self.receivedMOTD(self.motd)

    def irc_RPL_CREATED(self, prefix, params):
        self.created(params[1])
    
    def irc_RPL_YOURHOST(self, prefix, params):
        self.yourHost(params[1])
    
    def irc_RPL_MYINFO(self, prefix, params):
        self.myInfo(*params[1:5])
    
    def irc_RPL_BOUNCE(self, prefix, params):
        # 005 is doubly assigned.  Piece of crap dirty trash protocol.
        if params[-1] == "are available on this server":
            self.isupport(params[1:-1])
        else:
            self.bounce(params[1])
    
    def irc_RPL_LUSERCLIENT(self, prefix, params):
        self.luserClient(params[1])
    
    def irc_RPL_LUSEROP(self, prefix, params):
        try:
            self.luserOp(int(params[1]))
        except ValueError:
            pass
    
    def irc_RPL_LUSERCHANNELS(self, prefix, params):
        try:
            self.luserChannels(int(params[1]))
        except ValueError:
            pass
    
    def irc_RPL_LUSERME(self, prefix, params):
        self.luserMe(params[1])

    def irc_unknown(self, prefix, command, params):
        pass

    ### Receiving a CTCP query from another party
    ### It is safe to leave these alone.

    def ctcpQuery(self, user, channel, messages):
        """Dispatch method for any CTCP queries received.
        """
        for m in messages:
            method = getattr(self, "ctcpQuery_%s" % m[0], None)
            if method:
                method(user, channel, m[1])
            else:
                self.ctcpUnknownQuery(user, channel, m[0], m[1])

    def ctcpQuery_ACTION(self, user, channel, data):
        self.action(user, channel, data)

    def ctcpQuery_PING(self, user, channel, data):
        nick = string.split(user,"!")[0]
        self.ctcpMakeReply(nick, [("PING", data)])

    def ctcpQuery_FINGER(self, user, channel, data):
        if data is not None:
            self.quirkyMessage("Why did %s send '%s' with a FINGER query?"
                               % (user, data))
        if not self.fingerReply:
            return

        if callable(self.fingerReply):
            reply = self.fingerReply()
        else:
            reply = str(self.fingerReply)

        nick = string.split(user,"!")[0]
        self.ctcpMakeReply(nick, [('FINGER', reply)])

    def ctcpQuery_VERSION(self, user, channel, data):
        if data is not None:
            self.quirkyMessage("Why did %s send '%s' with a VERSION query?"
                               % (user, data))

        if self.versionName:
            nick = string.split(user,"!")[0]
            self.ctcpMakeReply(nick, [('VERSION', '%s:%s:%s' %
                                       (self.versionName,
                                        self.versionNum,
                                        self.versionEnv))])

    def ctcpQuery_SOURCE(self, user, channel, data):
        if data is not None:
            self.quirkyMessage("Why did %s send '%s' with a SOURCE query?"
                               % (user, data))
        if self.sourceURL:
            nick = string.split(user,"!")[0]
            # The CTCP document (Zeuge, Rollo, Mesander 1994) says that SOURCE
            # replies should be responded to with the location of an anonymous
            # FTP server in host:directory:file format.  I'm taking the liberty
            # of bringing it into the 21st century by sending a URL instead.
            self.ctcpMakeReply(nick, [('SOURCE', self.sourceURL),
                                      ('SOURCE', None)])

    def ctcpQuery_USERINFO(self, user, channel, data):
        if data is not None:
            self.quirkyMessage("Why did %s send '%s' with a USERINFO query?"
                               % (user, data))
        if self.userinfo:
            nick = string.split(user,"!")[0]
            self.ctcpMakeReply(nick, [('USERINFO', self.userinfo)])

    def ctcpQuery_CLIENTINFO(self, user, channel, data):
        """A master index of what CTCP tags this client knows.

        If no arguments are provided, respond with a list of known tags.
        If an argument is provided, provide human-readable help on
        the usage of that tag.
        """

        nick = string.split(user,"!")[0]
        if not data:
            # XXX: prefixedMethodNames gets methods from my *class*,
            # but it's entirely possible that this *instance* has more
            # methods.
            names = reflect.prefixedMethodNames(self.__class__,
                                                'ctcpQuery_')

            self.ctcpMakeReply(nick, [('CLIENTINFO',
                                       string.join(names, ' '))])
        else:
            args = string.split(data)
            method = getattr(self, 'ctcpQuery_%s' % (args[0],), None)
            if not method:
                self.ctcpMakeReply(nick, [('ERRMSG',
                                           "CLIENTINFO %s :"
                                           "Unknown query '%s'"
                                           % (data, args[0]))])
                return
            doc = getattr(method, '__doc__', '')
            self.ctcpMakeReply(nick, [('CLIENTINFO', doc)])


    def ctcpQuery_ERRMSG(self, user, channel, data):
        # Yeah, this seems strange, but that's what the spec says to do
        # when faced with an ERRMSG query (not a reply).
        nick = string.split(user,"!")[0]
        self.ctcpMakeReply(nick, [('ERRMSG',
                                   "%s :No error has occoured." % data)])

    def ctcpQuery_TIME(self, user, channel, data):
        if data is not None:
            self.quirkyMessage("Why did %s send '%s' with a TIME query?"
                               % (user, data))
        nick = string.split(user,"!")[0]
        self.ctcpMakeReply(nick,
                           [('TIME', ':%s' %
                             time.asctime(time.localtime(time.time())))])

    def ctcpQuery_DCC(self, user, channel, data):
        """Initiate a Direct Client Connection
        """

        if not data: return
        dcctype = data.split(None, 1)[0].upper()
        handler = getattr(self, "dcc_" + dcctype, None)
        if handler:
            data = data[len(dcctype)+1:]
            handler(user, channel, data)
        else:
            nick = string.split(user,"!")[0]
            self.ctcpMakeReply(nick, [('ERRMSG',
                                       "DCC %s :Unknown DCC type '%s'"
                                       % (data, dcctype))])
            self.quirkyMessage("%s offered unknown DCC type %s"
                               % (user, dcctype))

    def gotIncomingFile(self, incomingFile):
        """A DCC file transfer has been offered to us.

        Implement this method with your app-specific logic. By default we reject all incoming files.
        @param incomingFile: L{IncomingDccFile} instance.
        """
        incomingFile.reject()

    def dcc_TSEND(self, user, channel, data):
        self.dcc_SEND(user, channel, data, mode='turbo')

    def dcc_SEND(self, user, channel, data, mode='normal'):
        # Use splitQuoted for those who send files with spaces in the names.
        data = text.splitQuoted(data)
        if len(data) < 3:
            raise IRCBadMessage, "malformed DCC SEND request: %r" % (data,)

        (filename, address, port) = data[:3]

        for c in '/\\:': #security check
            if c in filename: raise IRCBadMessage, "in DCC SEND offer from %s: path information in filename: %s" % (user, filename)

        # security check, don't want to use filenames that are *too* long, they
        # could potentially cause a buffer overflow (as seen on Windows)
        if len(filename) > 100:
            raise IRCBadMessage, "in DCC SEND offer from %s: filename too long (>100): %s" % (user, filename)

        address = dccParseAddress(address)
        try:
            port = int(port)
        except ValueError:
            raise IRCBadMessage, "Indecipherable port %r" % (port,)

        size = -1
        if len(data) >= 4:
            try:
                size = int(data[3])
            except ValueError:
                pass

        incomingFile = self.incomingDccFileClass(self, user, address, port, filename, size, mode)
        self._incomingDccFiles.append(incomingFile)
        self.gotIncomingFile(incomingFile)
 
    def dcc_ACCEPT(self, user, channel, data):
        data = text.splitQuoted(data)
        if len(data) < 3:
            raise IRCBadMessage, "malformed DCC SEND ACCEPT request: %r" % (data,)
        (filename, port, resumePos) = data[:3]
        try:
            port = int(port)
            resumePos = int(resumePos)
        except ValueError:
            return

        #lets find the incomingFile that was waiting for this
        for f in self.incomingDccFiles:
            if f.user == user and f.port == port and resumePos == f.resumePos:
                f._resumeRequestAccepted()
                return
        log.msg("Odd, we got a DCC ACCEPT, but couldn't find a matching incomingFile")

    def sendFile(self, srcfile, user, mode='fast', resumable=True):
        """Offer a file to a remote user.
       
        If srcfile is a path, we will attempt to open it immediately. IOError will raise if that fails. Otherwise an instance of OutgoingDccFile will be returned. You may use it's 'deferred' attribute if needed. It will callback once the file has been successfully sent, or errback if something bad happend along the way.

        @param srcfile: A file path to open and use, or a file-like-object that data will be read from
        @type srcfile: C{str} or file-like-object
        @param user: The plain username to send to (without hostmask)
        @type user: C{str}
        @param mode: The DCC sending mode to use. May be one of 'slow', 'fast', or 'turbo'. Slow mode waits for each dcc ack before sending more data. Fast mode uses a send-ahead method where it may write more blocks of data before receiving the dcc ack for the previous block(s). Turbo mode uses the alternate 'DCC TSEND' method, and if the remote client supports this, then they won't send us any dcc ack's.
        @type mode: C{str}
        @param resumable: If True, we will try our best to service any 'DCC RESUME' requests. Otherwise such requests are ignored.
        @type resumable: C{bool}
        @rtype: L{OutgoingDccFile} instance.
        @raise IOError: If srcfile is a path, and opening it fails.
        """

        # need to get a file-object if we weren't passed one
        if type(srcfile) == types.StringType:
            file_obj = file(srcfile, 'rb')
        elif hasattr(srcfile, 'read'):
            file_obj = srcfile
        else:
            raise "srcfile must be a string or file-like-object"

        outgoingFile = self.outgoingDccFileClass(file_obj, user, self, mode, resumable)
        self._outgoingDccFiles.append(outgoingFile)
        return outgoingFile

    def dcc_RESUME(self, user, channel, data):
        data = text.splitQuoted(data)
        if len(data) < 3:
            raise IRCBadMessage, "malformed DCC SEND RESUME request: %r" % (data,)
        (filename, port, resumePos) = data[:3]
        try:
            port = int(port)
            resumePos = int(resumePos)
        except ValueError:
            return
        # lets see which outgoingFile this goes to
        for f in self._outgoingDccFiles:
            if f.user == user and f.port == port:
                f._gotResumeRequest(filename, resumePos)
                return

    def dcc_CHAT(self, user, channel, data):
        data = text.splitQuoted(data)
        if len(data) < 3:
            raise IRCBadMessage, "malformed DCC CHAT request: %r" % (data,)

        (filename, address, port) = data[:3]

        address = dccParseAddress(address)
        try:
            port = int(port)
        except ValueError:
            raise IRCBadMessage, "Indecipherable port %r" % (port,)

        self.dccDoChat(user, channel, address, port, data)

    ### The dccDo methods are the slightly higher-level siblings of
    ### common dcc_ methods; the arguments have been parsed for them.

    def dccDoResume(self, user, file, port, resumePos):
        """Called when a client is trying to resume an offered file
        via DCC send.  It should be either replied to with a DCC
        ACCEPT or ignored (default)."""
        pass

    def dccDoChat(self, user, channel, address, port, data):
        pass
        #factory = DccChatFactory(self, queryData=(user, channel, data))
        #reactor.connectTCP(address, port, factory)
        #self.dcc_sessions.append(factory)

    #def ctcpQuery_SED(self, user, data):
    #    """Simple Encryption Doodoo
    #
    #    Feel free to implement this, but no specification is available.
    #    """
    #    raise NotImplementedError

    def ctcpUnknownQuery(self, user, channel, tag, data):
        nick = string.split(user,"!")[0]
        self.ctcpMakeReply(nick, [('ERRMSG',
                                   "%s %s: Unknown query '%s'"
                                   % (tag, data, tag))])

        log.msg("Unknown CTCP query from %s: %s %s\n"
                 % (user, tag, data))

    def ctcpMakeReply(self, user, messages):
        """Send one or more X{extended messages} as a CTCP reply.

        @type messages: a list of extended messages.  An extended
        message is a (tag, data) tuple, where 'data' may be C{None}.
        """
        self.notice(user, ctcpStringify(messages))

    ### client CTCP query commands

    def ctcpMakeQuery(self, user, messages):
        """Send one or more X{extended messages} as a CTCP query.

        @type messages: a list of extended messages.  An extended
        message is a (tag, data) tuple, where 'data' may be C{None}.
        """
        self.msg(user, ctcpStringify(messages))

    ### Receiving a response to a CTCP query (presumably to one we made)
    ### You may want to add methods here, or override UnknownReply.

    def ctcpReply(self, user, channel, messages):
        """Dispatch method for any CTCP replies received.
        """
        for m in messages:
            method = getattr(self, "ctcpReply_%s" % m[0], None)
            if method:
                method(user, channel, m[1])
            else:
                self.ctcpUnknownReply(user, channel, m[0], m[1])

    def ctcpReply_PING(self, user, channel, data):
        nick = user.split('!', 1)[0]
        if (not self._pings) or (not self._pings.has_key((nick, data))):
            raise IRCBadMessage,\
                  "Bogus PING response from %s: %s" % (user, data)

        t0 = self._pings[(nick, data)]
        self.pong(user, time.time() - t0)

    def ctcpUnknownReply(self, user, channel, tag, data):
        """Called when a fitting ctcpReply_ method is not found.

        XXX: If the client makes arbitrary CTCP queries,
        this method should probably show the responses to
        them instead of treating them as anomolies.
        """
        log.msg("Unknown CTCP reply from %s: %s %s\n"
                 % (user, tag, data))

    ### Error handlers
    ### You may override these with something more appropriate to your UI.

    def badMessage(self, line, excType, excValue, tb):
        """When I get a message that's so broken I can't use it.
        """
        log.msg(line)
        log.msg(string.join(traceback.format_exception(excType,
                                                        excValue,
                                                        tb),''))

    def quirkyMessage(self, s):
        """This is called when I receive a message which is peculiar,
        but not wholly indecipherable.
        """
        log.msg(s + '\n')

    ### Protocool methods

    def connectionMade(self):
        self._queue = []
        if self.performLogin:
            self.register(self.nickname)

    def dataReceived(self, data):
        basic.LineReceiver.dataReceived(self, data.replace('\r', ''))

    def lineReceived(self, line):
        line = lowDequote(line)
        try:
            prefix, command, params = parsemsg(line)
            if numeric_to_symbolic.has_key(command):
                command = numeric_to_symbolic[command]
            self.handleCommand(command, prefix, params)
        except IRCBadMessage:
            self.badMessage(line, *sys.exc_info())


    def handleCommand(self, command, prefix, params):
        """Determine the function to call for the given command and call
        it with the given arguments.
        """
        method = getattr(self, "irc_%s" % command, None)
        try:
            if method is not None:
                method(prefix, params)
            else:
                self.irc_unknown(prefix, command, params)
        except:
            log.deferr()


    def __getstate__(self):
        dct = self.__dict__.copy()
        dct['_pings'] = None
        return dct

def dccParseAddress(address):
    if '.' in address:
        pass
    else:
        try:
            address = long(address)
        except ValueError:
            raise IRCBadMessage,\
                  "Indecipherable address %r" % (address,)
        else:
            address = (
                (address >> 24) & 0xFF,
                (address >> 16) & 0xFF,
                (address >> 8) & 0xFF,
                address & 0xFF,
                )
            address = '.'.join(map(str,address))
    return address


def fileSize(file):
    """I'll try my damndest to determine the size of this file object."""
    size = None
    if hasattr(file, "fileno"):
        fileno = file.fileno()
        try:
            stat_ = os.fstat(fileno)
            size = stat_[stat.ST_SIZE]
        except:
            pass
        else:
            return size

    if hasattr(file, "name") and path.exists(file.name):
        try:
            size = path.getsize(file.name)
        except:
            pass
        else:
            return size

    if hasattr(file, "seek") and hasattr(file, "tell"):
        try:
            try:
                cur_pos = file.tell()
                file.seek(0, 2)
                size = file.tell()
            finally:
                file.seek(cur_pos, 0)
        except:
            pass
        else:
            return size
    return size


class DccChat(basic.LineReceiver, styles.Ephemeral):
    """Direct Client Connection protocol type CHAT.

    DCC CHAT is really just your run o' the mill basic.LineReceiver
    protocol.  This class only varies from that slightly, accepting
    either LF or CR LF for a line delimeter for incoming messages
    while always using CR LF for outgoing.

    The lineReceived method implemented here uses the DCC connection's
    'client' attribute (provided upon construction) to deliver incoming
    lines from the DCC chat via IRCClient's normal privmsg interface.
    That's something of a spoof, which you may well want to override.
    """

    queryData = None
    delimiter = CR + NL
    client = None
    remoteParty = None
    buffer = ""

    def __init__(self, client, queryData=None):
        """Initialize a new DCC CHAT session.

        queryData is a 3-tuple of
        (fromUser, targetUserOrChannel, data)
        as received by the CTCP query.

        (To be honest, fromUser is the only thing that's currently
        used here. targetUserOrChannel is potentially useful, while
        the 'data' argument is soley for informational purposes.)
        """
        self.client = client
        if queryData:
            self.queryData = queryData
            self.remoteParty = self.queryData[0]

    def dataReceived(self, data):
        self.buffer = self.buffer + data
        lines = string.split(self.buffer, LF)
        # Put the (possibly empty) element after the last LF back in the
        # buffer
        self.buffer = lines.pop()

        for line in lines:
            if line[-1] == CR:
                line = line[:-1]
            self.lineReceived(line)

    def lineReceived(self, line):
        log.msg("DCC CHAT<%s> %s" % (self.remoteParty, line))
        self.client.privmsg(self.remoteParty,
                            self.client.nickname, line)


class DccChatFactory(protocol.ClientFactory):
    protocol = DccChat
    noisy = 0

    def __init__(self, client, queryData):
        self.client = client
        self.queryData = queryData

    def buildProtocol(self, addr):
        p = self.protocol(client=self.client, queryData=self.queryData)
        p.factory = self

    def clientConnectionFailed(self, unused_connector, unused_reason):
        self.client.dcc_sessions.remove(self)

    def clientConnectionLost(self, unused_connector, unused_reason):
        self.client.dcc_sessions.remove(self)


def dccDescribe(data):
    """Given the data chunk from a DCC query, return a descriptive string.
    """

    orig_data = data
    data = string.split(data)
    if len(data) < 4:
        return orig_data

    (dcctype, arg, address, port) = data[:4]

    if '.' in address:
        pass
    else:
        try:
            address = long(address)
        except ValueError:
            pass
        else:
            address = (
                (address >> 24) & 0xFF,
                (address >> 16) & 0xFF,
                (address >> 8) & 0xFF,
                address & 0xFF,
                )
            # The mapping to 'int' is to get rid of those accursed
            # "L"s which python 1.5.2 puts on the end of longs.
            address = string.join(map(str,map(int,address)), ".")

    if dcctype == 'SEND':
        filename = arg

        size_txt = ''
        if len(data) >= 5:
            try:
                size = int(data[4])
                size_txt = ' of size %d bytes' % (size,)
            except ValueError:
                pass

        dcc_text = ("SEND for file '%s'%s at host %s, port %s"
                    % (filename, size_txt, address, port))
    elif dcctype == 'CHAT':
        dcc_text = ("CHAT for host %s, port %s"
                    % (address, port))
    else:
        dcc_text = orig_data

    return dcc_text


# CTCP constants and helper functions

X_DELIM = chr(001)

def ctcpExtract(message):
    """Extract CTCP data from a string.

    Returns a dictionary with two items:

       - C{'extended'}: a list of CTCP (tag, data) tuples
       - C{'normal'}: a list of strings which were not inside a CTCP delimeter
    """

    extended_messages = []
    normal_messages = []
    retval = {'extended': extended_messages,
              'normal': normal_messages }

    messages = string.split(message, X_DELIM)
    odd = 0

    # X1 extended data X2 nomal data X3 extended data X4 normal...
    while messages:
        if odd:
            extended_messages.append(messages.pop(0))
        else:
            normal_messages.append(messages.pop(0))
        odd = not odd

    extended_messages[:] = filter(None, extended_messages)
    normal_messages[:] = filter(None, normal_messages)

    extended_messages[:] = map(ctcpDequote, extended_messages)
    for i in xrange(len(extended_messages)):
        m = string.split(extended_messages[i], SPC, 1)
        tag = m[0]
        if len(m) > 1:
            data = m[1]
        else:
            data = None

        extended_messages[i] = (tag, data)

    return retval

# CTCP escaping

M_QUOTE= chr(020)

mQuoteTable = {
    NUL: M_QUOTE + '0',
    NL: M_QUOTE + 'n',
    CR: M_QUOTE + 'r',
    M_QUOTE: M_QUOTE + M_QUOTE
    }

mDequoteTable = {}
for k, v in mQuoteTable.items():
    mDequoteTable[v[-1]] = k
del k, v

mEscape_re = re.compile('%s.' % (re.escape(M_QUOTE),), re.DOTALL)

def lowQuote(s):
    for c in (M_QUOTE, NUL, NL, CR):
        s = string.replace(s, c, mQuoteTable[c])
    return s

def lowDequote(s):
    def sub(matchobj, mDequoteTable=mDequoteTable):
        s = matchobj.group()[1]
        try:
            s = mDequoteTable[s]
        except KeyError:
            s = s
        return s

    return mEscape_re.sub(sub, s)

X_QUOTE = chr(0134)

xQuoteTable = {
    X_DELIM: X_QUOTE + 'a',
    X_QUOTE: X_QUOTE + X_QUOTE
    }

xDequoteTable = {}

for k, v in xQuoteTable.items():
    xDequoteTable[v[-1]] = k

xEscape_re = re.compile('%s.' % (re.escape(X_QUOTE),), re.DOTALL)

def ctcpQuote(s):
    for c in (X_QUOTE, X_DELIM):
        s = string.replace(s, c, xQuoteTable[c])
    return s

def ctcpDequote(s):
    def sub(matchobj, xDequoteTable=xDequoteTable):
        s = matchobj.group()[1]
        try:
            s = xDequoteTable[s]
        except KeyError:
            s = s
        return s

    return xEscape_re.sub(sub, s)

def ctcpStringify(messages):
    """
    @type messages: a list of extended messages.  An extended
    message is a (tag, data) tuple, where 'data' may be C{None}, a
    string, or a list of strings to be joined with whitespace.

    @returns: String
    """
    coded_messages = []
    for (tag, data) in messages:
        if data:
            if not isinstance(data, types.StringType):
                try:
                    # data as list-of-strings
                    data = " ".join(map(str, data))
                except TypeError:
                    # No?  Then use it's %s representation.
                    pass
            m = "%s %s" % (tag, data)
        else:
            m = str(tag)
        m = ctcpQuote(m)
        m = "%s%s%s" % (X_DELIM, m, X_DELIM)
        coded_messages.append(m)

    line = string.join(coded_messages, '')
    return line


# Constants (from RFC 2812)
RPL_WELCOME = '001'
RPL_YOURHOST = '002'
RPL_CREATED = '003'
RPL_MYINFO = '004'
RPL_BOUNCE = '005'
RPL_USERHOST = '302'
RPL_ISON = '303'
RPL_AWAY = '301'
RPL_UNAWAY = '305'
RPL_NOWAWAY = '306'
RPL_WHOISUSER = '311'
RPL_WHOISSERVER = '312'
RPL_WHOISOPERATOR = '313'
RPL_WHOISIDLE = '317'
RPL_ENDOFWHOIS = '318'
RPL_WHOISCHANNELS = '319'
RPL_WHOWASUSER = '314'
RPL_ENDOFWHOWAS = '369'
RPL_LISTSTART = '321'
RPL_LIST = '322'
RPL_LISTEND = '323'
RPL_UNIQOPIS = '325'
RPL_CHANNELMODEIS = '324'
RPL_NOTOPIC = '331'
RPL_TOPIC = '332'
RPL_INVITING = '341'
RPL_SUMMONING = '342'
RPL_INVITELIST = '346'
RPL_ENDOFINVITELIST = '347'
RPL_EXCEPTLIST = '348'
RPL_ENDOFEXCEPTLIST = '349'
RPL_VERSION = '351'
RPL_WHOREPLY = '352'
RPL_ENDOFWHO = '315'
RPL_NAMREPLY = '353'
RPL_ENDOFNAMES = '366'
RPL_LINKS = '364'
RPL_ENDOFLINKS = '365'
RPL_BANLIST = '367'
RPL_ENDOFBANLIST = '368'
RPL_INFO = '371'
RPL_ENDOFINFO = '374'
RPL_MOTDSTART = '375'
RPL_MOTD = '372'
RPL_ENDOFMOTD = '376'
RPL_YOUREOPER = '381'
RPL_REHASHING = '382'
RPL_YOURESERVICE = '383'
RPL_TIME = '391'
RPL_USERSSTART = '392'
RPL_USERS = '393'
RPL_ENDOFUSERS = '394'
RPL_NOUSERS = '395'
RPL_TRACELINK = '200'
RPL_TRACECONNECTING = '201'
RPL_TRACEHANDSHAKE = '202'
RPL_TRACEUNKNOWN = '203'
RPL_TRACEOPERATOR = '204'
RPL_TRACEUSER = '205'
RPL_TRACESERVER = '206'
RPL_TRACESERVICE = '207'
RPL_TRACENEWTYPE = '208'
RPL_TRACECLASS = '209'
RPL_TRACERECONNECT = '210'
RPL_TRACELOG = '261'
RPL_TRACEEND = '262'
RPL_STATSLINKINFO = '211'
RPL_STATSCOMMANDS = '212'
RPL_ENDOFSTATS = '219'
RPL_STATSUPTIME = '242'
RPL_STATSOLINE = '243'
RPL_UMODEIS = '221'
RPL_SERVLIST = '234'
RPL_SERVLISTEND = '235'
RPL_LUSERCLIENT = '251'
RPL_LUSEROP = '252'
RPL_LUSERUNKNOWN = '253'
RPL_LUSERCHANNELS = '254'
RPL_LUSERME = '255'
RPL_ADMINME = '256'
RPL_ADMINLOC = '257'
RPL_ADMINLOC = '258'
RPL_ADMINEMAIL = '259'
RPL_TRYAGAIN = '263'
ERR_NOSUCHNICK = '401'
ERR_NOSUCHSERVER = '402'
ERR_NOSUCHCHANNEL = '403'
ERR_CANNOTSENDTOCHAN = '404'
ERR_TOOMANYCHANNELS = '405'
ERR_WASNOSUCHNICK = '406'
ERR_TOOMANYTARGETS = '407'
ERR_NOSUCHSERVICE = '408'
ERR_NOORIGIN = '409'
ERR_NORECIPIENT = '411'
ERR_NOTEXTTOSEND = '412'
ERR_NOTOPLEVEL = '413'
ERR_WILDTOPLEVEL = '414'
ERR_BADMASK = '415'
ERR_UNKNOWNCOMMAND = '421'
ERR_NOMOTD = '422'
ERR_NOADMININFO = '423'
ERR_FILEERROR = '424'
ERR_NONICKNAMEGIVEN = '431'
ERR_ERRONEUSNICKNAME = '432'
ERR_NICKNAMEINUSE = '433'
ERR_NICKCOLLISION = '436'
ERR_UNAVAILRESOURCE = '437'
ERR_USERNOTINCHANNEL = '441'
ERR_NOTONCHANNEL = '442'
ERR_USERONCHANNEL = '443'
ERR_NOLOGIN = '444'
ERR_SUMMONDISABLED = '445'
ERR_USERSDISABLED = '446'
ERR_NOTREGISTERED = '451'
ERR_NEEDMOREPARAMS = '461'
ERR_ALREADYREGISTRED = '462'
ERR_NOPERMFORHOST = '463'
ERR_PASSWDMISMATCH = '464'
ERR_YOUREBANNEDCREEP = '465'
ERR_YOUWILLBEBANNED = '466'
ERR_KEYSET = '467'
ERR_CHANNELISFULL = '471'
ERR_UNKNOWNMODE = '472'
ERR_INVITEONLYCHAN = '473'
ERR_BANNEDFROMCHAN = '474'
ERR_BADCHANNELKEY = '475'
ERR_BADCHANMASK = '476'
ERR_NOCHANMODES = '477'
ERR_BANLISTFULL = '478'
ERR_NOPRIVILEGES = '481'
ERR_CHANOPRIVSNEEDED = '482'
ERR_CANTKILLSERVER = '483'
ERR_RESTRICTED = '484'
ERR_UNIQOPPRIVSNEEDED = '485'
ERR_NOOPERHOST = '491'
ERR_NOSERVICEHOST = '492'
ERR_UMODEUNKNOWNFLAG = '501'
ERR_USERSDONTMATCH = '502'

# And hey, as long as the strings are already intern'd...
symbolic_to_numeric = {
    "RPL_WELCOME": '001',
    "RPL_YOURHOST": '002',
    "RPL_CREATED": '003',
    "RPL_MYINFO": '004',
    "RPL_BOUNCE": '005',
    "RPL_USERHOST": '302',
    "RPL_ISON": '303',
    "RPL_AWAY": '301',
    "RPL_UNAWAY": '305',
    "RPL_NOWAWAY": '306',
    "RPL_WHOISUSER": '311',
    "RPL_WHOISSERVER": '312',
    "RPL_WHOISOPERATOR": '313',
    "RPL_WHOISIDLE": '317',
    "RPL_ENDOFWHOIS": '318',
    "RPL_WHOISCHANNELS": '319',
    "RPL_WHOWASUSER": '314',
    "RPL_ENDOFWHOWAS": '369',
    "RPL_LISTSTART": '321',
    "RPL_LIST": '322',
    "RPL_LISTEND": '323',
    "RPL_UNIQOPIS": '325',
    "RPL_CHANNELMODEIS": '324',
    "RPL_NOTOPIC": '331',
    "RPL_TOPIC": '332',
    "RPL_INVITING": '341',
    "RPL_SUMMONING": '342',
    "RPL_INVITELIST": '346',
    "RPL_ENDOFINVITELIST": '347',
    "RPL_EXCEPTLIST": '348',
    "RPL_ENDOFEXCEPTLIST": '349',
    "RPL_VERSION": '351',
    "RPL_WHOREPLY": '352',
    "RPL_ENDOFWHO": '315',
    "RPL_NAMREPLY": '353',
    "RPL_ENDOFNAMES": '366',
    "RPL_LINKS": '364',
    "RPL_ENDOFLINKS": '365',
    "RPL_BANLIST": '367',
    "RPL_ENDOFBANLIST": '368',
    "RPL_INFO": '371',
    "RPL_ENDOFINFO": '374',
    "RPL_MOTDSTART": '375',
    "RPL_MOTD": '372',
    "RPL_ENDOFMOTD": '376',
    "RPL_YOUREOPER": '381',
    "RPL_REHASHING": '382',
    "RPL_YOURESERVICE": '383',
    "RPL_TIME": '391',
    "RPL_USERSSTART": '392',
    "RPL_USERS": '393',
    "RPL_ENDOFUSERS": '394',
    "RPL_NOUSERS": '395',
    "RPL_TRACELINK": '200',
    "RPL_TRACECONNECTING": '201',
    "RPL_TRACEHANDSHAKE": '202',
    "RPL_TRACEUNKNOWN": '203',
    "RPL_TRACEOPERATOR": '204',
    "RPL_TRACEUSER": '205',
    "RPL_TRACESERVER": '206',
    "RPL_TRACESERVICE": '207',
    "RPL_TRACENEWTYPE": '208',
    "RPL_TRACECLASS": '209',
    "RPL_TRACERECONNECT": '210',
    "RPL_TRACELOG": '261',
    "RPL_TRACEEND": '262',
    "RPL_STATSLINKINFO": '211',
    "RPL_STATSCOMMANDS": '212',
    "RPL_ENDOFSTATS": '219',
    "RPL_STATSUPTIME": '242',
    "RPL_STATSOLINE": '243',
    "RPL_UMODEIS": '221',
    "RPL_SERVLIST": '234',
    "RPL_SERVLISTEND": '235',
    "RPL_LUSERCLIENT": '251',
    "RPL_LUSEROP": '252',
    "RPL_LUSERUNKNOWN": '253',
    "RPL_LUSERCHANNELS": '254',
    "RPL_LUSERME": '255',
    "RPL_ADMINME": '256',
    "RPL_ADMINLOC": '257',
    "RPL_ADMINLOC": '258',
    "RPL_ADMINEMAIL": '259',
    "RPL_TRYAGAIN": '263',
    "ERR_NOSUCHNICK": '401',
    "ERR_NOSUCHSERVER": '402',
    "ERR_NOSUCHCHANNEL": '403',
    "ERR_CANNOTSENDTOCHAN": '404',
    "ERR_TOOMANYCHANNELS": '405',
    "ERR_WASNOSUCHNICK": '406',
    "ERR_TOOMANYTARGETS": '407',
    "ERR_NOSUCHSERVICE": '408',
    "ERR_NOORIGIN": '409',
    "ERR_NORECIPIENT": '411',
    "ERR_NOTEXTTOSEND": '412',
    "ERR_NOTOPLEVEL": '413',
    "ERR_WILDTOPLEVEL": '414',
    "ERR_BADMASK": '415',
    "ERR_UNKNOWNCOMMAND": '421',
    "ERR_NOMOTD": '422',
    "ERR_NOADMININFO": '423',
    "ERR_FILEERROR": '424',
    "ERR_NONICKNAMEGIVEN": '431',
    "ERR_ERRONEUSNICKNAME": '432',
    "ERR_NICKNAMEINUSE": '433',
    "ERR_NICKCOLLISION": '436',
    "ERR_UNAVAILRESOURCE": '437',
    "ERR_USERNOTINCHANNEL": '441',
    "ERR_NOTONCHANNEL": '442',
    "ERR_USERONCHANNEL": '443',
    "ERR_NOLOGIN": '444',
    "ERR_SUMMONDISABLED": '445',
    "ERR_USERSDISABLED": '446',
    "ERR_NOTREGISTERED": '451',
    "ERR_NEEDMOREPARAMS": '461',
    "ERR_ALREADYREGISTRED": '462',
    "ERR_NOPERMFORHOST": '463',
    "ERR_PASSWDMISMATCH": '464',
    "ERR_YOUREBANNEDCREEP": '465',
    "ERR_YOUWILLBEBANNED": '466',
    "ERR_KEYSET": '467',
    "ERR_CHANNELISFULL": '471',
    "ERR_UNKNOWNMODE": '472',
    "ERR_INVITEONLYCHAN": '473',
    "ERR_BANNEDFROMCHAN": '474',
    "ERR_BADCHANNELKEY": '475',
    "ERR_BADCHANMASK": '476',
    "ERR_NOCHANMODES": '477',
    "ERR_BANLISTFULL": '478',
    "ERR_NOPRIVILEGES": '481',
    "ERR_CHANOPRIVSNEEDED": '482',
    "ERR_CANTKILLSERVER": '483',
    "ERR_RESTRICTED": '484',
    "ERR_UNIQOPPRIVSNEEDED": '485',
    "ERR_NOOPERHOST": '491',
    "ERR_NOSERVICEHOST": '492',
    "ERR_UMODEUNKNOWNFLAG": '501',
    "ERR_USERSDONTMATCH": '502',
}

numeric_to_symbolic = {}
for k, v in symbolic_to_numeric.items():
    numeric_to_symbolic[v] = k
