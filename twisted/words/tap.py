
# Copyright (c) 2001-2004 Twisted Matrix Laboratories.
# See LICENSE for details.


"""
I am a support module for creating chat servers with mktap.
"""

from twisted.python import usage, plugin
from twisted.spread import pb
from twisted.spread.util import LocalAsyncForwarder
from twisted.words import service, ircservice, webwords
from twisted.web import server
from twisted.cred.authorizer import DefaultAuthorizer

import sys, string

botTypeList = plugin.getPlugIns("twisted.words.bot")
botTypes = {}
for bott in botTypeList:
    botTypes[bott.botType] = bott

class Options(usage.Options):
    synopsis = "Usage: mktap words [options]"
    optParameters = [["irc", "i", "6667", "Port to run the IRC server on."],
                     ["irchost", "h", '', "Host to bind IRC server to."],
                     ["wordshost", "b", '', "Host to bind Words service to."],
                     ["webhost", "s", '', "Host to bind web interface to."],
                     ["port", "p", str(pb.portno),
                      "Port to run the Words service on."],
                     ["web", "w", "8080",
                      "Port to run the web interface on."]]
    bots = None
    def opt_bot(self, option):
        """Specify a bot-plugin to load; this should be in the format
        'plugin:nickname'.
        """
        if self.bots is None:
            self.bots = []
        botplugnm, botnickname = string.split(option, ":")
        self.bots.append((botnickname, botTypes[botplugnm].load()))

    users = None
    def opt_user(self, option):
        """Specify a user/password combination to add to the authorizer and
        chat service immediately.
        """
        if self.users is None:
            self.users = []
        self.users.append(option.split(":"))
    opt_bot.__doc__ = opt_bot.__doc__ + ("plugin types are: %s" % string.join(botTypes.keys(), ' '))
    longdesc = "Makes a twisted.words service and support servers."

def updateApplication(app, config):
    auth = DefaultAuthorizer(app)
    svc = service.Service("twisted.words", app, auth)
    bkr = pb.BrokerFactory(pb.AuthRoot(auth))
    irc = ircservice.IRCGateway(svc)
    adm = server.Site(webwords.WordsGadget(svc))

    if config.bots:
        for nickname, plug in config.bots:
            svc.addBot(nickname, plug.createBot())
    if config.users:
        for username, pw in config.users:
            svc.createPerspective(username).makeIdentity(pw)

    app.listenTCP(int(config['port']), bkr, interface=config['wordshost'])
    app.listenTCP(int(config['irc']), irc, interface=config['irchost'])
    app.listenTCP(int(config['web']), adm, interface=config['webhost'])
