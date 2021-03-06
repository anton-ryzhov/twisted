
# Copyright (c) 2001-2004 Twisted Matrix Laboratories.
# See LICENSE for details.


"""Test cases for 'jelly' object serialization.
"""

from twisted.spread import jelly

from twisted.test import test_newjelly

class JellyTestCase(test_newjelly.JellyTestCase):
    jc = jelly

    def testPersistentStorage(self):
        perst = [{}, 1]
        def persistentStore(obj, jel, perst = perst):
            perst[1] = perst[1] + 1
            perst[0][perst[1]] = obj
            return str(perst[1])

        def persistentLoad(pidstr, unj, perst = perst):
            pid = int(pidstr)
            return perst[0][pid]

        SimpleJellyTest = test_newjelly.SimpleJellyTest
        a = SimpleJellyTest(1, 2)
        b = SimpleJellyTest(3, 4)
        c = SimpleJellyTest(5, 6)

        a.b = b
        a.c = c
        c.b = b

        jel = self.jc.jelly(a, persistentStore = persistentStore)
        x = self.jc.unjelly(jel, persistentLoad = persistentLoad)

        self.assertIdentical(x.b, x.c.b)
        # assert len(perst) == 3, "persistentStore should only be called 3 times."
        self.failUnless(perst[0], "persistentStore was not called.")
        self.assertIdentical(x.b, a.b, "Persistent storage identity failure.")

class CircularReferenceTestCase(test_newjelly.CircularReferenceTestCase):
    jc = jelly


testCases = [JellyTestCase, CircularReferenceTestCase]
