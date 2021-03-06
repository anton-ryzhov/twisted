
# Copyright (c) 2001-2004 Twisted Matrix Laboratories.
# See LICENSE for details.


"""
Test cases for twisted.reflect module.
"""

import weakref

# Twisted Imports
from twisted.trial import unittest
from twisted.python import reflect


class SettableTest(unittest.TestCase):
    def setUp(self):
        self.setter = reflect.Settable()

    def tearDown(self):
        del self.setter

    def testSet(self):
        self.setter(a=1, b=2)
        self.failUnlessEqual(self.setter.a, 1)
        self.failUnlessEqual(self.setter.b, 2)


class AccessorTester(reflect.Accessor):
    def set_x(self, x):
        self.y = x
        self.reallySet('x',x)

    def get_z(self):
        self.q = 1
        return 1

    def del_z(self):
        self.reallyDel("q")


class AccessorTest(unittest.TestCase):
    def setUp(self):
        self.tester = AccessorTester()

    def testSet(self):
        self.tester.x = 1
        self.failUnlessEqual(self.tester.x, 1)
        self.failUnlessEqual(self.tester.y, 1)

    def testGet(self):
        self.failUnlessEqual(self.tester.z, 1)
        self.failUnlessEqual(self.tester.q, 1)

    def testDel(self):
        self.tester.z
        self.failUnlessEqual(self.tester.q, 1)
        del self.tester.z
        self.failUnlessEqual(hasattr(self.tester, "q"), 0)
        self.tester.x = 1
        del self.tester.x
        self.failUnlessEqual(hasattr(self.tester, "x"), 0)


class LookupsTestCase(unittest.TestCase):
    """Test lookup methods."""

    def testClassLookup(self):
        self.assertEquals(reflect.namedClass("twisted.python.reflect.Summer"), reflect.Summer)

    def testModuleLookup(self):
        self.assertEquals(reflect.namedModule("twisted.python.reflect"), reflect)

class LookupsTestCaseII(unittest.TestCase):
    def testPackageLookup(self):
        import twisted.python
        self.failUnlessIdentical(reflect.namedAny("twisted.python"),
                                 twisted.python)

    def testModuleLookup(self):
        self.failUnlessIdentical(reflect.namedAny("twisted.python.reflect"),
                                 reflect)

    def testClassLookup(self):
        self.failUnlessIdentical(reflect.namedAny("twisted.python."
                                                  "reflect.Summer"),
                                 reflect.Summer)

    def testAttributeLookup(self):
        # Why does Identical break down here?
        self.failUnlessEqual(reflect.namedAny("twisted.python."
                                              "reflect.Summer.reallySet"),
                             reflect.Summer.reallySet)

    def testSecondAttributeLookup(self):
        self.failUnlessIdentical(reflect.namedAny("twisted.python."
                                                  "reflect.Summer."
                                                  "reallySet.__doc__"),
                                 reflect.Summer.reallySet.__doc__)

class ObjectGrep(unittest.TestCase):
    def testDictionary(self):
        o = object()
        d1 = {None: o}
        d2 = {o: None}
        
        self.assertIn("[None]", reflect.objgrep(d1, o, reflect.isSame))
        self.assertIn("{None}", reflect.objgrep(d2, o, reflect.isSame))
    
    def testList(self):
        o = object()
        L = [None, o]
        
        self.assertIn("[1]", reflect.objgrep(L, o, reflect.isSame))
    
    def testTuple(self):
        o = object()
        T = (o, None)
        
        self.assertIn("[0]", reflect.objgrep(T, o, reflect.isSame))
    
    def testInstance(self):
        class Dummy:
            pass
        o = object()
        d = Dummy()
        d.o = o
        
        self.assertIn(".o", reflect.objgrep(d, o, reflect.isSame))
    
    def testWeakref(self):
        class Dummy:
            pass
        o = Dummy()
        w1 = weakref.ref(o)

        self.assertIn("()", reflect.objgrep(w1, o, reflect.isSame))

    def testBoundMethod(self):
        class Dummy:
            def dummy(self):
                pass
        o = Dummy()
        m = o.dummy
        
        self.assertIn(".im_self", reflect.objgrep(m, m.im_self, reflect.isSame))
        self.assertIn(".im_class", reflect.objgrep(m, m.im_class, reflect.isSame))
        self.assertIn(".im_func", reflect.objgrep(m, m.im_func, reflect.isSame))

    def testEverything(self):
        class Dummy:
            def method(self):
                pass
        
        o = Dummy()
        D1 = {(): "baz", None: "Quux", o: "Foosh"}
        L = [None, (), D1, 3]
        T = (L, {}, Dummy())
        D2 = {0: "foo", 1: "bar", 2: T}
        i = Dummy()
        i.attr = D2
        m = i.method
        w = weakref.ref(m)
        
        self.assertIn("().im_self.attr[2][0][2]{'Foosh'}", reflect.objgrep(w, o, reflect.isSame))

class GetClass(unittest.TestCase):
	def testOld(self):
		class OldClass:
			pass
		old = OldClass()
		self.assertIn(reflect.getClass(OldClass).__name__, ('class', 'classobj'))
		self.assertEquals(reflect.getClass(old).__name__, 'OldClass')

	def testNew(self):
		class NewClass(object):
			pass
		new = NewClass()
		self.assertEquals(reflect.getClass(NewClass).__name__, 'type')
		self.assertEquals(reflect.getClass(new).__name__, 'NewClass')
		
