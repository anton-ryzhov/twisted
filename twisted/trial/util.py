# -*- test-case-name: twisted.test.test_trial -*-
# Copyright (c) 2001-2004 Twisted Matrix Laboratories.
# See LICENSE for details.

#
# -*- test-case-name: twisted.test.test_trial -*-

import traceback, warnings, new, inspect
from twisted.python import components, failure
from twisted.internet import interfaces

# Methods in this list will be omitted from a failed test's traceback if
# they are the final frame.
_failureConditionals = [
    'fail', 'failIf', 'failUnless', 'failUnlessRaises', 'failUnlessEqual',
    'failUnlessIdentical', 'failIfEqual', 'assertApproximates']


def reactorCleanUp():
    from twisted.internet import reactor
    reactor.iterate() # flush short-range timers
    pending = reactor.getDelayedCalls()
    if pending:
        msg = "\npendingTimedCalls still pending:\n"
        for p in pending:
            msg += " %s\n" % p
        from warnings import warn
        warn(msg)
        for p in pending: p.cancel() # delete the rest
        reactor.iterate() # flush them
        raise unittest.FailTest, msg
    if interfaces.IReactorThreads.providedBy(reactor):
        reactor.suggestThreadPoolSize(0)
        if hasattr(reactor, 'threadpool') and reactor.threadpool:
            reactor.threadpool.stop()
            reactor.threadpool = None

def isTestClass(testClass):
    return issubclass(testClass, unittest.TestCase)

def isTestCase(testCase):
    return isinstance(testCase, unittest.TestCase)

def _append(result, lst):
    lst.append(result)

def _getDeferredResult(d, timeout=None):
    from twisted.internet import reactor
    if timeout is not None:
        d.setTimeout(timeout)
    resultSet = []
    d.addBoth(_append, resultSet)
    while not resultSet:
        reactor.iterate()
    return resultSet[0]

def deferredResult(d, timeout=None):
    """Waits for a Deferred to arrive, then returns or throws an exception,
    based on the result.
    """
    result = _getDeferredResult(d, timeout)
    if isinstance(result, failure.Failure):
        raise result
    else:
        return result

def wait(d, timeout=10):
    """This function is unstable.

    Waits (spins the reactor) for a Deferred to arrive, then returns
    or throws an exception, based on the result. The difference
    between this and deferredResult is that it actually throws the
    original exception, not the Failure, so synchronous exception
    handling is much more sane.
    """
    result = _getDeferredResult(d, timeout)
    if isinstance(result, failure.Failure):
        result.raiseException()
    else:
        return result
    

def deferredError(d, timeout=None):
    """Waits for deferred to fail, and it returns the Failure.

    If the deferred succeeds, raises FailTest.
    """
    result = _getDeferredResult(d, timeout)
    if isinstance(result, failure.Failure):
        return result
    else:
        raise unittest.FailTest, "Deferred did not fail: %r" % (result,)


def extract_tb(tb, limit=None):
    """Extract a list of frames from a traceback, without unittest internals.

    Functionally identical to L{traceback.extract_tb}, but cropped to just
    the test case itself, excluding frames that are part of the Trial
    testing framework.
    """
    l = traceback.extract_tb(tb, limit)
    util_file = __file__.replace('.pyc','.py')
    unittest_file = unittest.__file__.replace('.pyc','.py')
    runner_file = runner.__file__.replace('.pyc','.py')
    framework = [(unittest_file, '_runPhase'), # Tester._runPhase
                 (unittest_file, '_main'),     # Tester._main
                 (runner_file, 'runTest'),     # [ITestRunner].runTest
                 ]
    # filename, line, funcname, sourcetext
    while (l[0][0], l[0][2]) in framework:
        del l[0]

    if (l[-1][0] == unittest_file) and (l[-1][2] in _failureConditionals):
        del l[-1]
    return l

def format_exception(eType, eValue, tb, limit=None):
    """A formatted traceback and exception, without exposing the framework.

    I am identical in function to L{traceback.format_exception},
    but I screen out frames from the traceback that are part of
    the testing framework itself, leaving only the code being tested.
    """
    result = [x.strip()+'\n' for x in
              failure.Failure(eValue,eType,tb).getBriefTraceback().split('\n')]
    return result
    # Only mess with tracebacks if they are from an explicitly failed
    # test.
    if eType != unittest.FailTest:
        return traceback.format_exception(eType, eValue, tb, limit)

    tb_list = extract_tb(tb, limit)

    l = ["Traceback (most recent call last):\n"]
    l.extend(traceback.format_list(tb_list))
    l.extend(traceback.format_exception_only(eType, eValue))
    return l

def suppressWarnings(f, *warningz):
    def enclosingScope(warnings, warningz):
        exec """def %s(*args, **kwargs):
    for warning in warningz:
        warnings.filterwarnings('ignore', *warning)
    try:
        return f(*args, **kwargs)
    finally:
        for warning in warningz:
            warnings.filterwarnings('default', *warning)
""" % (f.func_name,) in locals()
        return locals()[f.func_name]
    return enclosingScope(warnings, warningz)


    
# sibling imports, ugh.
import unittest
import runner
