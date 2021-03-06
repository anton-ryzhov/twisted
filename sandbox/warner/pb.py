#! /usr/bin/python

import weakref, types
try:
    import cStringIO as StringIO
except ImportError:
    import StringIO

from twisted.python import failure, log
from twisted.python.components import registerAdapter
from twisted.internet import defer, protocol, reactor

import slicer, schema, tokens, banana, flavors
from tokens import BananaError, Violation, ISlicer
from slicer import BaseUnslicer, ReferenceSlicer
ScopedSlicer = slicer.ScopedSlicer
from flavors import getRemoteInterfaces
from flavors import Copyable, RemoteCopy, registerRemoteCopy
from flavors import RemoteInterfaceRegistry

# names we import so that others can reach them as pb.foo
from flavors import RemoteInterface, Referenceable

class PendingRequest(object):
    active = True
    def __init__(self, reqID):
        self.reqID = reqID
        self.deferred = defer.Deferred()
        self.constraint = None # this constrains the results
    def setConstraint(self, constraint):
        self.constraint = constraint
    def complete(self, res):
        if self.active:
            self.active = False
            self.deferred.callback(res)
        else:
            log.msg("PendingRequest.complete called on an inactive request")
    def fail(self, why):
        if self.active:
            self.active = False
            self.failure = why
            self.deferred.errback(why)
        else:
            log.msg("multiple failures")
            log.msg("first one was:", self.failure)
            log.msg("this one was:", why)
            log.err("multiple failures indicate a problem")

class RemoteReference(object):
    def __init__(self, broker, refID, interfaceNames):
        self.broker = broker
        self.refID = refID
        self.interfaceNames = interfaceNames

    def __del__(self):
        self.broker.freeRemoteReference(self.refID)

    def callRemote(self, _name, *args, **kwargs):
        # there are two forms:
        #  rr.callRemote(RIFoo['bar'], **kwargs): uses a RemoteInterface to
        #    describe the method being called. This will enforce argument
        #    constraints and let you to tricky clever things in the future.
        #  rr.callRemote('bar', **kwargs): does not use a RemoteInterface,
        #    even if the other end is using them.

        # Note: for consistency, *all* failures are reported asynchronously.

        req = None

        _resultConstraint = kwargs.get("_resultConstraint", "none")
        # remember that "none" is not a valid constraint, so we use it to
        # mean "not set by the caller", which means we fall back to whatever
        # the RemoteInterface says. Using None would mean an AnyConstraint,
        # which is not the same thing.

        if _resultConstraint != "none":
            del kwargs["_resultConstraint"]

        try:
            # newRequestID() could fail with a DeadReferenceError
            reqID = self.broker.newRequestID()
        except:
            d = defer.Deferred()
            d.errback(failure.Failure())
            return d

        try:
            # in this clause, we validate the outbound arguments against our
            # notion of what the other end will accept (the RemoteInterface)
            req = PendingRequest(reqID)

            # first, figure out which method they want to invoke
            interfaceName = ""
            methodName = None
            methodSchema = None

            if type(_name) == str:
                methodName = _name
            elif schema.IRemoteMethodConstraint.providedBy(_name):
                # they're using the rr.callRemote(RIFoo['bar'], **kw) form
                methodSchema = _name
                interfaceName = methodSchema.interface.__remote_name__
                if self.interfaceNames:
                    # if they call with an interface, and it looks like the
                    # target is using interfaces, they must claim to support
                    # it
                    if interfaceName not in self.interfaceNames:
                        raise Violation("%s does not offer %s" % \
                                        (self, interfaceName))
                methodName = methodSchema.name
            else:
                raise NameError("could not get remote method name from %s" \
                                % _name)

            if methodSchema:
                # turn positional arguments into kwargs. mapArguments() could
                # fail for bad argument names or missing required parameters
                argsdict = methodSchema.mapArguments(args, kwargs)

                # check args against the arg constraint. This could fail if
                # any arguments are of the wrong type
                methodSchema.checkAllArgs(kwargs)

                # the Interface gets to constraint the return value too, so
                # make a note of it to use later
                req.setConstraint(methodSchema.getResponseConstraint())
            else:
                if args:
                    why = "positional arguments require a RemoteInterface"
                    why += " for %s.%s()" % (self, methodName)
                    raise tokens.BananaError(why)
                argsdict = kwargs

            # if the caller specified a _resultConstraint, that overrides
            # the schema's one
            if _resultConstraint != "none":
                # overrides schema
                req.setConstraint(schema.makeConstraint(_resultConstraint))

        except: # TODO: merge this with the next try/except clause
            # we have not yet sent anything to the far end. A failure here
            # is entirely local: stale broker, bad method name, bad
            # arguments. We abandon the PendingRequest, but errback the
            # Deferred it was going to use
            req.fail(failure.Failure())
            return req.deferred

        try:
            # once we start sending the CallSlicer, we could get either a
            # local or a remote failure, so we must be prepared to accept an
            # answer. After this point, we assign all responsibility to the
            # PendingRequest structure.
            self.broker.addRequest(req)

            # TODO: there is a decidability problem here: if the reqID made
            # it through, the other end will send us an answer (possibly an
            # error if the remaining slices were aborted). If not, we will
            # not get an answer. To decide whether we should remove our
            # broker.waitingForAnswers[] entry, we need to know how far the
            # slicing process made it.

            slicer = CallSlicer(reqID, self.refID, interfaceName, methodName,
                                argsdict)

            # this could fail if any of the arguments (or their children)
            # are unsliceable
            d = self.broker.send(slicer)
            # d will fire when the last argument has been serialized. It
            # will errback if the arguments could not be serialized. We need
            # to catch this case and errback the caller.

        except:
            req.fail(failure.Failure())
            return req.deferred

        # if we got here, we have been able to start serializing the
        # arguments. If serialization fails, the PendingRequest needs to be
        # flunked (because we aren't guaranteed that the far end will do it).

        d.addErrback(self.broker.gotError, req)

        # the remote end could send back an error response for many reasons:
        #  bad method name
        #  bad argument types (violated their schema)
        #  exception during method execution
        #  method result violated the results schema
        # something else could occur to cause an errback:
        #  connection lost before response completely received
        #  exception during deserialization of the response
        #   [but only if it occurs after the reqID is received]
        #  method result violated our results schema
        # if none of those occurred, the callback will be run

        return req.deferred

    def notifyOnDisconnect(self, callback):
        self.broker.notifyOnDisconnect(callback)
    def dontNotifyOnDisconnect(self, callback):
        self.broker.dontNotifyOnDisconnect(callback)

registerAdapter(flavors.YourReferenceSlicer, RemoteReference, ISlicer)

class URLRemoteReference(RemoteReference):
    # Just like RemoteReference, but refID is a string. These are created by
    # Broker.remoteReferenceForName when we use a PB URL to refer to someone
    # else's object. We use a different class to reduce the confusion when a
    # URLRemoteReference emerges from a round-trip as an unrelated
    # RemoteReference
    pass
registerAdapter(flavors.YourReferenceSlicer, URLRemoteReference, ISlicer)


class DecRefUnslicer(BaseUnslicer):
    refID = None

    def checkToken(self, typebyte, size):
        if self.refID is None:
            if typebyte != tokens.INT:
                raise BananaError("reference ID must be an INT")
        else:
            raise BananaError("stop talking already!")

    def receiveChild(self, token):
        # TODO: log but otherwise ignore
        self.refID = token

    def receiveClose(self):
        if self.refID is None:
            raise BananaError("sequence ended too early")
        return self.broker.decref(self.refID)

    def describe(self):
        if self.refID is None:
            return "<decref-?>"
        return "<decref-%s>" % self.refID

class CallUnslicer(BaseUnslicer):
    # 0:reqID, 1:objID, 2:interfacename, 3:methodname, 4: [(argname/value)]..
    stage = 0
    reqID = None
    obj = None
    interface = None
    methodname = None
    methodSchema = None # will be a MethodArgumentsConstraint
    argname = None
    argConstraint = None

    def start(self, count):
        self.args = {}

    def checkToken(self, typebyte, size):
        # TODO: limit strings by returning a number instead of None
        if self.stage == 0:
            if typebyte != tokens.INT:
                raise BananaError("request ID must be an INT")
        elif self.stage == 1:
            if typebyte not in (tokens.INT, tokens.STRING, tokens.VOCAB):
                raise BananaError("object ID must be an INT or STRING")
        elif self.stage == 2:
            if typebyte not in (tokens.STRING, tokens.VOCAB):
                raise BananaError("interface name must be a STRING")
            # TODO: limit to longest interface name of self.obj?
        elif self.stage == 3:
            if typebyte not in (tokens.STRING, tokens.VOCAB):
                raise BananaError("method name must be a STRING")
            # TODO: limit to longest method name of self.obj in the interface
        elif self.stage == 4:
            if self.argname == None:
                if typebyte not in (tokens.STRING, tokens.VOCAB):
                    raise BananaError("argument name must be a STRING")
                # TODO: limit to the longest argname in the method
            else:
                if self.argConstraint:
                    self.argConstraint.checkToken(typebyte, size)

    def doOpen(self, opentype):
        # checkToken insures that this can only happen when we're receiving
        # an argument value, so we don't have to bother checking self.stage
        # or self.argname
        if self.argConstraint:
            self.argConstraint.checkOpentype(opentype)
        unslicer = self.open(opentype)
        if unslicer:
            if self.argConstraint:
                unslicer.setConstraint(self.argConstraint)
        return unslicer

    def reportViolation(self, f):
        # if the Violation is because we received an ABORT, then we know
        # that the sender knows there was a problem, so don't respond.
        if f.value.args[0] == "ABORT received":
            return f

        # if the Violation was raised after we know the reqID, we can send
        # back an Error.
        if self.stage > 0:
            self.broker.callFailed(f, self.reqID)
        return f # give up our sequence

    def receiveChild(self, token):
        #print "CallUnslicer.receiveChild [s%d]" % self.stage, repr(token)
        # TODO: if possible, return an error to the other side
        if self.stage == 0: # reqID
            # we don't yet know which reqID to send any failure to
            self.reqID = token
            self.stage += 1
            assert not self.broker.activeLocalCalls.get(self.reqID)
            self.broker.activeLocalCalls[self.reqID] = self
            return

        if self.stage == 1: # objID
            # this might raise an exception if objID is invalid
            self.obj = self.broker.getReferenceable(token)
            self.stage += 1

        elif self.stage == 2: # interfacename (or "")
            # validate the interfacename. This may raise an exception for
            # unknown interfaces.
            if token != "":
                try:
                    iface = self.broker.getRemoteInterfaceByName(token)
                    self.interface = iface
                except KeyError:
                    raise Violation("unknown interface %s" % token)
            if self.interface and not self.interface.providedBy(self.obj):
                raise Violation("object %s does not implement %s" % \
                                (self.obj, token))
            self.stage += 1

        elif self.stage == 3: # methodname
            # validate the methodname, get the schema. This may raise an
            # exception for unknown methods
            methodname = token
            # must find the schema, using the interfaces
            
            # TODO: getSchema should probably be in an adapter instead of in
            # a pb.Referenceable base class. Old-style (unconstrained)
            # flavors.Referenceable should be adapted to something which
            # always returns None

            # TODO: make this faster. A likely optimization is to take a
            # tuple of components.getInterfaces(obj) and use it as a cache
            # key. It would be even faster to use obj.__class__, but that
            # would probably violate the expectation that instances can
            # define their own __implements__ (independently from their
            # class). If this expectation were to go away, a quick
            # obj.__class__ -> RemoteReferenceSchema cache could be built.

            ms = None

            if self.interface:
                # they are calling an interface+method pair
                ms = self.interface.get(methodname)
                if not ms:
                    why = "method '%s' not defined in %s" % \
                          (methodname, self.interface.__remote_name__)
                    raise Violation(why)
            else:
                # they are calling a method without specifying an interface.
                # If the target uses RemoteInterfaces at all, then the method
                # must be defined by one of them. If the target does not use
                # RemoteInterfaces, then it must be some sort of legacy
                # thingy and we just accept the method anyway (unless the
                # Broker refuses to accept non-constrained methods).
                ifaces = flavors.getRemoteInterfaces(self.obj)
                if ifaces:
                    ms = self.broker.getSchemaForMethod(ifaces, methodname)
                    if not ms:
                        why = "method '%s' not defined in any of %s" \
                              % (methodname, [i.__remote_name__
                                              for i in ifaces])
                        raise Violation(why)

            self.methodSchema = ms
            self.methodname = methodname

            if self.broker.requireSchema and not self.methodSchema:
                why = "This broker does not accept unconstrained method calls"
                raise Violation(why)

            self.stage += 1

        elif self.stage == 4: # argname/value pairs
            if self.argname == None:
                argname = token
                if self.args.has_key(argname):
                    raise BananaError("duplicate argument '%s'" % argname)
                ms = self.methodSchema
                if ms:
                    # if the argname is invalid, this may raise Violation
                    accept, self.argConstraint = ms.getArgConstraint(argname)
                    assert accept # TODO: discard if not
                self.argname = argname
            else:
                argvalue = token
                self.args[self.argname] = argvalue
                self.argname = None

    def receiveClose(self):
        if self.stage != 4 or self.argname != None:
            raise BananaError("'call' sequence ended too early")
        self.stage = 5
        if self.methodSchema:
            # ask them again so they can look for missing arguments
            self.methodSchema.checkArgs(self.args)
        # this is where we actually call the method. doCall must now take
        # responsibility for the request (specifically for catching any
        # exceptions and doing callFailed)
        self.broker.doCall(self.reqID, self.obj, self.methodname,
                           self.args, self.methodSchema)

    def describe(self):
        s = "<methodcall"
        if self.stage == 0:
            pass
        if self.stage == 1:
            s += " reqID=%d" % self.reqID
        if self.stage == 2:
            s += " obj=%s" % (self.obj,)
        if self.stage == 3:
            ifacename = "[none]"
            if self.interface:
                ifacename = self.interface.__remote_name__
            s += " iface=%s" % ifacename
        if self.stage == 4:
            s += " .%s" % self.methodname
            if self.argname != None:
                s += " arg[%s]" % self.argname
        if self.stage == 5:
            s += " .close"
        s += ">"
        return s

class AnswerUnslicer(BaseUnslicer):
    request = None
    resultConstraint = None
    haveResults = False

    def checkToken(self, typebyte, size):
        if self.request == None:
            if typebyte != tokens.INT:
                raise BananaError("request ID must be an INT")
        elif not self.haveResults:
            if self.resultConstraint:
                try:
                    self.resultConstraint.checkToken(typebyte, size)
                except Violation, v:
                    # improve the error message
                    if v.args:
                        # this += gives me a TypeError "object doesn't
                        # support item assignment", which confuses me
                        #v.args[0] += " in inbound method results"
                        why = v.args[0] + " in inbound method results"
                        v.args = why,
                    else:
                        v.args = ("in inbound method results",)
                    raise v # this will errback the request
        else:
            raise BananaError("stop sending me stuff!")

    def doOpen(self, opentype):
        if self.resultConstraint:
            self.resultConstraint.checkOpentype(opentype)
            # TODO: improve the error message
        unslicer = self.open(opentype)
        if unslicer:
            if self.resultConstraint:
                unslicer.setConstraint(self.resultConstraint)
        return unslicer

    def receiveChild(self, token):
        if self.request == None:
            reqID = token
            # may raise Violation for bad reqIDs
            self.request = self.broker.getRequest(reqID)
            self.resultConstraint = self.request.constraint
        else:
            self.results = token
            self.haveResults = True

    def reportViolation(self, f):
        # if the Violation was received after we got the reqID, we can tell
        # the broker it was an error
        if self.request != None:
            self.broker.gotError(f, self.request)
        return f # give up our sequence

    def receiveClose(self):
        self.broker.gotAnswer(self.results, self.request)

    def describe(self):
        if self.request:
            return "Answer(req=%s)" % self.request.reqID
        return "Answer(req=?)"

class ErrorUnslicer(BaseUnslicer):
    request = None
    fConstraint = schema.FailureConstraint()
    gotFailure = False

    def checkToken(self, typebyte, size):
        if self.request == None:
            if typebyte != tokens.INT:
                raise BananaError("request ID must be an INT")
        elif not self.gotFailure:
            self.fConstraint.checkToken(typebyte, size)
        else:
            raise BananaError("stop sending me stuff!")

    def doOpen(self, opentype):
        self.fConstraint.checkOpentype(opentype)
        unslicer = self.open(opentype)
        if unslicer:
            unslicer.setConstraint(self.fConstraint)
        return unslicer

    def reportViolation(self, f):
        # a failure while receiving the failure. A bit daft, really.
        if self.request != None:
            self.broker.gotError(f, self.request)
        return f # give up our sequence

    def receiveChild(self, token):
        if self.request == None:
            reqID = token
            # may raise BananaError for bad reqIDs
            self.request = self.broker.getRequest(reqID)
        else:
            self.failure = token
            self.gotFailure = True

    def receiveClose(self):
        self.broker.gotError(self.failure, self.request)

    def describe(self):
        if self.request is None:
            return "<error-?>"
        return "<error-%s>" % self.request.reqID


PBTopRegistry = {
    ("decref",): DecRefUnslicer,
    ("call",): CallUnslicer,
    ("answer",): AnswerUnslicer,
    ("error",): ErrorUnslicer,
    }

PBOpenRegistry = {
    ('my-reference',): flavors.ReferenceUnslicer,
    ('your-reference',): flavors.YourReferenceUnslicer,
    # ('copyable', classname) is handled inline, through the CopyableRegistry
    }

class PBRootUnslicer(slicer.RootUnslicer):
    # topRegistry defines what objects are allowed at the top-level
    topRegistry = [PBTopRegistry]
    # openRegistry defines what objects are allowed at the second level and
    # below
    openRegistry = [slicer.UnslicerRegistry, PBOpenRegistry]
    logViolations = False

    def checkToken(self, typebyte, size):
        if typebyte != tokens.OPEN:
            raise BananaError("top-level must be OPEN")

    def openerCheckToken(self, typebyte, size, opentype):
        if typebyte == tokens.STRING:
            if len(opentype) == 0:
                if size > self.maxIndexLength:
                    why = "first opentype STRING token is too long, %d>%d" % \
                          (size, self.maxIndexLength)
                    raise Violation(why)
            if opentype == ("copyable",):
                # TODO: this is silly, of course (should pre-compute maxlen)
                maxlen = reduce(max,
                                [len(cname) \
                                 for cname in flavors.CopyableRegistry.keys()]
                                )
                if size > maxlen:
                    why = "copyable-classname token is too long, %d>%d" % \
                          (size, maxlen)
                    raise Violation(why)
        elif typebyte == tokens.VOCAB:
            return
        else:
            # TODO: hack for testing
            raise Violation("index token 0x%02x not STRING or VOCAB" % \
                              ord(typebyte))
            raise BananaError("index token 0x%02x not STRING or VOCAB" % \
                              ord(typebyte))
        
    def open(self, opentype):
        # used for lower-level objects, delegated up from childunslicer.open
        assert len(self.protocol.receiveStack) > 1
        if opentype[0] == 'copyable':
            if len(opentype) > 1:
                classname = opentype[1]
                try:
                    factory = flavors.CopyableRegistry[classname]
                except KeyError:
                    raise Violation("unknown RemoteCopy class '%s'" \
                                    % classname)
                if tokens.IUnslicer.implementedBy(factory):
                    child = factory()
                    child.broker = self.broker
                    return child
                if flavors.IRemoteCopy.implementedBy(factory):
                    if factory.nonCyclic:
                        child = flavors.NonCyclicRemoteCopyUnslicer(factory)
                    else:
                        child = flavors.RemoteCopyUnslicer(factory)
                    child.broker = self.broker
                    return child
                why = "RemoteCopy class '%s' has weird factory %s" \
                                % (classname, factory)
                raise Violation(why)
            else:
                return None # still need classname
        for reg in self.openRegistry:
            opener = reg.get(opentype)
            if opener is not None:
                child = opener()
                break
        else:
            raise Violation("unknown OPEN type %s" % (opentype,))
        child.broker = self.broker
        return child

    def doOpen(self, opentype):
        child = slicer.RootUnslicer.doOpen(self, opentype)
        if child:
            child.broker = self.broker
        return child

    def reportViolation(self, f):
        if self.logViolations:
            print "hey, something failed:", f
        return None # absorb the failure

    def receiveChild(self, obj):
        pass

class AnswerSlicer(ScopedSlicer):
    opentype = ('answer',)

    def __init__(self, reqID, results):
        ScopedSlicer.__init__(self, None)
        self.reqID = reqID
        self.results = results

    def sliceBody(self, streamable, banana):
        yield self.reqID
        yield self.results

    def describe(self):
        return "<answer-%s>" % self.reqID

class ErrorSlicer(ScopedSlicer):
    opentype = ('error',)

    def __init__(self, reqID, f):
        ScopedSlicer.__init__(self, None)
        assert isinstance(f, failure.Failure)
        self.reqID = reqID
        self.f = f

    def sliceBody(self, streamable, banana):
        yield self.reqID
        yield self.f

    def describe(self):
        return "<error-%s>" % self.reqID

# failures are sent as Copyables
class FailureSlicer(slicer.BaseSlicer):
    slices = failure.Failure
    classname = "twisted.python.failure.Failure"

    def slice(self, streamable, banana):
        self.streamable = streamable
        yield 'copyable'
        yield self.classname
        state = self.getStateToCopy(self.obj, banana)
        for k,v in state.iteritems():
            yield k
            yield v
    def describe(self):
        return "<%s>" % self.classname
        
    def getStateToCopy(self, obj, broker):
        #state = obj.__dict__.copy()
        #state['tb'] = None
        #state['frames'] = []
        #state['stack'] = []

        state = {}
        if isinstance(obj.value, failure.Failure):
            # TODO: how can this happen? I got rid of failure2Copyable, so
            # if this case is possible, something needs to replace it
            raise RuntimeError("not implemented yet")
            #state['value'] = failure2Copyable(obj.value, banana.unsafeTracebacks)
        else:
            state['value'] = str(obj.value) # Exception instance
        state['type'] = str(obj.type) # Exception class
        if broker.unsafeTracebacks:
            io = StringIO.StringIO()
            obj.printTraceback(io)
            state['traceback'] = io.getvalue()
            # TODO: provide something with globals and locals and HTML and
            # all that cool stuff
        else:
            state['traceback'] = 'Traceback unavailable\n'
        if len(state['traceback']) > 1900:
            state['traceback'] = (state['traceback'][:1900] +
                                  "\n\n-- TRACEBACK TRUNCATED --\n")
        state['parents'] = obj.parents
        return state

class CopiedFailure(failure.Failure, RemoteCopy):
    """I am a shadow of some remote Failure instance. I contain less
    information than the original did.

    You can still extract a (brief) printable traceback from me. My .parents
    attribute is a list of strings describing the class of the exception
    that I contain, just like the real Failure had, so my trap() and check()
    methods work fine. My .type and .value attributes are string
    representations of the original exception class and exception instance,
    respectively. The most significant effect is that you cannot access
    f.value.args, and should instead just use f.value .

    My .frames and .stack attributes are empty, although this may change in
    the future (and with the cooperation of the sender).
    """

    nonCyclic = True
    stateSchema = schema.FailureConstraint()

    def __init__(self):
        RemoteCopy.__init__(self)

    def setCopyableState(self, state):
        self.__dict__ = state
        # state includes: type, value, traceback, parents
        self.tb = None
        self.frames = []
        self.stack = []

    pickled = 1
    def printTraceback(self, file=None):
        if not file: file = log.logfile
        file.write("Traceback from remote host -- ")
        file.write(self.traceback)

    printBriefTraceback = printTraceback
    printDetailedTraceback = printTraceback
registerRemoteCopy(FailureSlicer.classname, CopiedFailure)

class DecRefSlicer(slicer.BaseSlicer):
    opentype = ('decref',)
    def __init__(self, refID):
        self.refID = refID
    def sliceBody(self, streamable, banana):
        yield self.refID
    def describe(self):
        return "<decref-%s>" % self.refID

class CallSlicer(ScopedSlicer):
    opentype = ('call',)

    def __init__(self, reqID, refID, interfacename, methodname, args):
        ScopedSlicer.__init__(self, None)
        self.reqID = reqID
        self.refID = refID
        self.interfacename = interfacename # could be None, represented by ""
        self.methodname = methodname
        self.args = args

    def sliceBody(self, streamable, banana):
        yield self.reqID
        yield self.refID
        if self.interfacename:
            yield self.interfacename
        else:
            yield ""
        yield self.methodname
        keys = self.args.keys()
        keys.sort()
        for argname in keys:
            yield argname
            yield self.args[argname]

    def describe(self):
        return "<call-%s-%s-%s-%s>" % (self.reqID, self.refID,
                                       self.interfacename, self.methodname)

class PBRootSlicer(slicer.RootSlicer):
    def registerReference(self, refid, obj):
        assert 0


class Broker(banana.Banana):
    slicerClass = PBRootSlicer
    unslicerClass = PBRootUnslicer
    unsafeTracebacks = True
    requireSchema = False
    disconnected = False
    factory = None

    def __init__(self):
        banana.Banana.__init__(self)
        self.initBroker()

    def initBroker(self):
        self.rootSlicer.broker = self
        self.rootUnslicer.broker = self

        # sending side uses these
        self.currentLocalID = 0
        self.clids = {} # maps from puid to clid
        self.localObjects = {} # things which are available to our peer.
                               # These are reference counted and removed
                               # when the last decref message is received.
        # receiving side uses these
        self.remoteReferences = weakref.WeakValueDictionary() # clid to RR

        # sending side uses these
        self.currentRequestID = 0
        self.waitingForAnswers = {} # we wait for the other side to answer
        self.disconnectWatchers = []
        # receiving side uses these
        self.activeLocalCalls = {} # the other side wants an answer from us

    def connectionReady(self):
        if self.factory: # in tests we won't have factory
            self.factory.clientConnectionMade(self)

    def connectionLost(self, why):
        self.disconnected = True
        self.abandonAllRequests(why)
        dw = self.disconnectWatchers
        self.disconnectWatchers = []
        for d in dw:
            d()
        banana.Banana.connectionLost(self, why)

    def notifyOnDisconnect(self, callback):
        self.disconnectWatchers.append(callback)
    def dontNotifyOnDisconnect(self, callback):
        self.disconnectWatchers.remove(callback)

    # Referenceable handling, methods for the sending-side (the side that
    # holds the original Referenceable)

    def getCLID(self, puid, obj):
        # returns (clid, firstTime)
        clid = self.clids.get(puid, None)
        if clid is None:
            self.currentLocalID = self.currentLocalID + 1
            clid = self.currentLocalID
            self.clids[puid] = clid
            self.localObjects[clid] = obj
            return clid, True
        return clid, False

    def getReferenceable(self, clid):
        """clid is the connection-local ID of the Referenceable the other
        end is trying to invoke or point to. If it is a number, they want an
        implicitly-created per-connection object that we sent to them at
        some point in the past. If it is a string, they want an object that
        was registered with our Factory.
        """

        obj = None
        if type(clid) == int:
            obj = self.localObjects[clid]
            # obj = tokens.IReferenceable(obj)
            # assert isinstance(obj, pb.Referenceable)
            # obj needs .getMethodSchema, which needs .getArgConstraint
        elif type(clid) == str:
            if self.factory:
                obj = self.factory.getReferenceable(clid)
        return obj

    def decref(self, clid):
        # invoked when the other side sends us a decref message
        puid = self.localObjects[clid].processUniqueID()
        del self.clids[puid]
        del self.localObjects[clid]

    # Referenceable handling, methods for the receiving-side (the side that
    # holds the derived RemoteReference)

    def registerRemoteReference(self, clid, interfaceNames=[]):
        """The far end holds a Referenceable and has just sent us a
        reference to it (expressed as a small integer). If this is a new
        reference, they will give us an interface list too. Obtain a
        RemoteReference object (creating it if necessary) to give to the
        local recipient. There is exactly one RemoteReference object for
        each clid. We hold a weakref to the RemoteReference so we can
        provide the same object later but so we can detect when the Broker
        is the only thing left that knows about it.

        The sender remembers that we hold a reference to their object. When
        our RemoteReference goes away, its __del__ method will tell us to
        send a decref message so they can possibly free their object.
        """

        for i in interfaceNames:
            assert type(i) == str
        obj = self.remoteReferences.get(clid)
        if not obj:
            obj = RemoteReference(self, clid, interfaceNames)
            self.remoteReferences[clid] = obj  # WeakValueDictionary
        return obj

    def freeRemoteReference(self, clid):
        # this is called by RemoteReference.__del__

        # the WeakValueDictionary means we don't have to explicitly remove it
        #del self.remoteReferences[clid]

        if type(clid) != int:
            return # URL-refs aren't reference-counted

        try:
            self.send(DecRefSlicer(clid))
        except:
            log.msg("failure during freeRemoteReference")
            log.err()

    def remoteReferenceForName(self, name, interfaces):
        return URLRemoteReference(self, name, interfaces)

    # remote-method-invocation methods, calling side (RemoteReference):
    # RemoteReference.callRemote, gotAnswer, gotError

    def newRequestID(self):
        if self.disconnected:
            raise DeadReferenceError("Calling Stale Broker")
        self.currentRequestID = self.currentRequestID + 1
        return self.currentRequestID

    def addRequest(self, req):
        self.waitingForAnswers[req.reqID] = req

    def getRequest(self, reqID):
        try:
            return self.waitingForAnswers[reqID]
        except KeyError:
            raise Violation("non-existent reqID '%d'" % reqID)

    def gotAnswer(self, results, req):
        del self.waitingForAnswers[req.reqID]
        req.complete(results)
    def gotError(self, failure, req):
        del self.waitingForAnswers[req.reqID]
        req.fail(failure)
    def abandonAllRequests(self, why):
        for req in self.waitingForAnswers.values():
            req.fail(why)
        self.waitingForAnswers = {}


    # remote-method-invocation methods, target-side (Referenceable):
    # doCall, callFinished, callFailed

    def getRemoteInterfaceByName(self, riname):
        # this lives in the broker because it ought to be per-connection
        return flavors.RemoteInterfaceRegistry[riname]

    def getSchemaForMethod(self, rifaces, methodname):
        # this lives in the Broker so it can override the resolution order,
        # not that overlapping RemoteInterfaces should be allowed to happen
        # all that often
        for ri in rifaces:
            m = ri.get(methodname)
            if m:
                return m
        return None

    def doCall(self, reqID, obj, methodname, args, methodSchema):
        try:
            meth = getattr(obj, "remote_%s" % methodname)
            #if meth is None:
            #    raise Violation("method '%s' not defined" % methodname)
            res = meth(**args)
        except:
            f = failure.Failure()
            self.callFailed(f, reqID)
        else:
            if not isinstance(res, defer.Deferred):
                res = defer.succeed(res)
            # interesting case: if the method completes successfully, but
            # our schema prohibits us from sending the result (perhaps the
            # method returned an int but the schema insists upon a string).
            res.addCallback(self.callFinished, reqID, methodSchema)
            res.addErrback(self.callFailed, reqID)

    def callFinished(self, res, reqID, methodSchema):
        assert self.activeLocalCalls[reqID]
        if methodSchema:
            methodSchema.checkResults(res) # may raise Violation
        answer = AnswerSlicer(reqID, res)
        # once the answer has started transmitting, any exceptions must be
        # logged and dropped, and not turned into an Error to be sent.
        try:
            self.send(answer)
            # TODO: .send should return a Deferred that fires when the last
            # byte has been queued, and we should delete the local note then
        except:
            log.err()
        del self.activeLocalCalls[reqID]

    def callFailed(self, f, reqID):
        assert self.activeLocalCalls[reqID]
        self.send(ErrorSlicer(reqID, f))
        del self.activeLocalCalls[reqID]

import debug
class LoggingBroker(debug.LoggingBananaMixin, Broker):
    pass

class PBServerFactory(protocol.ServerFactory):
    
    protocol = Broker
    #protocol = LoggingBroker

    def __init__(self, root, unsafeTracebacks=True):
        self.localObjects = {}
        self.registerReferenceable("", root) # TODO: use IReferenceable(root)
        self.unsafeTracebacks = unsafeTracebacks

    def clientConnectionMade(self, broker):
        # dummy because Brokers always call them
        pass

    def buildProtocol(self, addr):
        """Return a Broker attached to me (as the service provider).
        """
        #print "building protocol"
        proto = self.protocol()
        #proto.doLog = " s"
        proto.factory = self
        proto.unsafeTracebacks = self.unsafeTracebacks
        return proto

    def registerReferenceable(self, name, obj):
        self.localObjects[name] = obj
    def getReferenceable(self, name):
        return self.localObjects.get(name, None)

class PBClientFactory(protocol.ClientFactory):
    """Client factory for PB brokers.

    As with all client factories, use with reactor.connectTCP/SSL/etc..
    getPerspective and getRootObject can be called either before or
    after the connect.
    """

    protocol = Broker
    #protocol = LoggingBroker

    def __init__(self):
        self._reset()

    def _reset(self):
        self.onConnect = [] # list of deferreds
        self._broker = None

    def _failAll(self, reason):
        deferreds = self.onConnect
        self._reset()
        for d in deferreds:
            d.errback(reason)

    def clientConnectionFailed(self, connector, reason):
        self._failAll(reason)

    def clientConnectionLost(self, connector, reason, reconnecting=0):
        """Reconnecting subclasses should call with reconnecting=1."""
        if reconnecting:
            # any pending requests will go to next connection attempt
            # so we don't fail them.
            self._broker = None
        else:
            self._failAll(reason)

    def clientConnectionMade(self, broker):
        self._broker = broker
        #broker.doLog = "c"
        ds = self.onConnect
        self.onConnect = []
        for d in ds:
            d.callback(self._broker)

    def getBroker(self):
        if self._broker and not self._broker.disconnected:
            return defer.succeed(self._broker)
        d = defer.Deferred()
        self.onConnect.append(d)
        return d

    def getObjectNamed(self, name, interfaces):
        # If called on a dead broker, you'll get a DeadReferenceError
        # exception.
        for i in interfaces:
            assert isinstance(i, flavors.RemoteInterfaceClass)
        # create a URLRemoteReference
        d = self.getBroker()
        d.addCallback(self._getObjectNamed, name, interfaces)
        return d
    def _getObjectNamed(self, broker, name, interfaces):
        return broker.remoteReferenceForName(name, interfaces)

    def getRootObject(self, interfaces):
        """Get root object of remote PB server. Assume it implements the
        given RemoteInterfaces.

        @return Deferred of the root object.
        """
        return self.getObjectNamed("", interfaces)

    def disconnect(self):
        """If the factory is connected, close the connection.

        Note that if you set up the factory to reconnect, you will need to
        implement extra logic to prevent automatic reconnection after this
        is called.
        """
        if self._broker:
            self._broker.transport.loseConnection()

def connect(host, port):
    f = PBClientFactory()
    d = f.getBroker()
    reactor.connectTCP(host, port, f)
    return d

def getRemoteURL_TCP(host, port, pathname, *interfaces):
    f = PBClientFactory()
    d = f.getObjectNamed(pathname, interfaces)
    reactor.connectTCP(host, port, f)
    return d

# callRemoteURL_TCP is temporary, for testing. Use callRemoteURL() instead.
def callRemoteURL_TCP(_host, _port, _pathname,
                      _interface, _methodname, **args):
    d = getRemoteURL_TCP(_host, _port, _pathname, _interface)
    d.addCallback(lambda ref: ref.callRemote(_methodname, **args))
    return d

# <glyph> warner: twisted.python.urlpath
# <glyph> warner: >>> URLPath.fromString("pb://stuff.com/1234")
# <glyph> URLPath(scheme='pb', netloc='', path='//stuff.com/1234', query='',
# fragment='')
# <glyph> oh wait
# <glyph> huh, that's not right
# <glyph> warner: you need to do urlparse.uses_netloc.append('pb')
# <glyph> but other than that, the parser in URLPath is fine

def getRemoteURL(url, *interfaces):
    raise NotImplementedError("glyph said he'd write this")

def callRemoteURL(_url, _interface, _methodname, **args):
    d = getRemoteURL(_url, _interface)
    d.addCallback(lambda ref: ref.callRemote(_methodname, **args))
    return d
