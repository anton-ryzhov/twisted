"""

A demo app that can protect arbitrarily deep hierarchies.

Try e.g. http://localhost:8081/secret/stuff/stuff/stuff/
without authenticating first.

Requirements:

- Main page and some subpages do not need authentication.

- There are multiple subpages that require authentication.

- Pages that require authentication must show a login dialog, and
  after a succesful login act as if user was logged in already.

- The subpages requiring authentication may be deeply linked into from
  each other or the non-authenticating pages.

- The authentication should be shared amongst all the pages.

"""

import os
from twisted.cred import checkers, portal, credentials
from twisted.web import static
from nevow import rend, loaders, inevow, guard, url

def getActionURL(current, root):
    assert root is not None
    root = root.pathList()
    me = current.pathList(copy=True)
    diff = len(me) - len(root)
    assert diff >= 0
    action = current
    if diff == 1:
        action = action.here()
    else:
        while diff > 1:
            diff -= 1
            action = action.parent()
    action = action.child(guard.LOGIN_AVATAR)
    for element in me[len(root):]:
        action = action.child(element)
    return action

class LoginPage(rend.Page):
    """The resource that is returned when you are not logged in"""
    docFactory = loaders.xmlfile(
        'login.xhtml',
        templateDir=os.path.split(os.path.abspath(__file__))[0])

    def locateChild(self, request, segments):
        return LoginPage(), []

    def render_form(self, context, data):
        request = context.locate(inevow.IRequest)
        current = url.URL.fromRequest(request)
        root = request.getComponent(inevow.ISessionRoot)
        action = getActionURL(current, root)
        context.fillSlots('action-url', str(action))
        return context.tag

class Authenticated(rend.Page):
    addSlash = True
    docFactory = loaders.xmlfile(
        'authenticated.xhtml',
        templateDir=os.path.split(os.path.abspath(__file__))[0])

    def data_name(self, context, data):
        request = context.locate(inevow.IRequest)
        return request.getSession().getLoggedInRoot().loggedIn

    def child_stuff(self, request):
        return self

class Another(rend.Page):
    addSlash = True
    template=""""""
    docFactory = loaders.xmlfile(
        'another.xhtml',
        templateDir=os.path.split(os.path.abspath(__file__))[0])

    def child_more(self, request):
        return self

class Public(rend.Page):
    addSlash = True
    docFactory = loaders.xmlfile(
        'public.xhtml',
        templateDir=os.path.split(os.path.abspath(__file__))[0])

    def child_secret(self, request):
        if not request.getSession().getLoggedInRoot().loggedIn:
            return LoginPage()
        return Authenticated()

class MainPage(rend.Page):
    addSlash = True
    docFactory = loaders.xmlfile(
        'main.xhtml',
        templateDir=os.path.split(os.path.abspath(__file__))[0])

    def __init__(self, loggedIn):
        self.loggedIn = loggedIn
        super(MainPage, self).__init__()

    def child_secret(self, request):
        if not request.getSession().getLoggedInRoot().loggedIn:
            return LoginPage()
        return Authenticated()

    def child_another(self, request):
        if not request.getSession().getLoggedInRoot().loggedIn:
            return LoginPage()
        return Another()

    def child_public(self, request):
        return Public()

class TODOGetRidOfMeRealm:
    __implements__ = portal.IRealm,

    def requestAvatar(self, avatarId, mind, *interfaces):
        if inevow.IResource not in interfaces:
            raise NotImplementedError, "no interface"

        if avatarId is checkers.ANONYMOUS:
            resource = MainPage(None)
            resource.realm = self
            return (inevow.IResource,
                    resource,
                    lambda: None)
        else:
            resource = MainPage(avatarId)
            resource.realm = self
            return (inevow.IResource,
                    resource,
                    lambda: None)

def createResource():
    realm = TODOGetRidOfMeRealm()
    porta = portal.Portal(realm)

    checker = checkers.InMemoryUsernamePasswordDatabaseDontUse(test="test")
    porta.registerChecker(checkers.AllowAnonymousAccess(), credentials.IAnonymous)
    porta.registerChecker(checker)

    top = static.Data('<a href="prefix/">click me</a>', 'text/html')
    top.putChild('', top)
    top.putChild('prefix', guard.SessionWrapper(porta))

    return top
