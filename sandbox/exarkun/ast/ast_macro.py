
import sys, copy, inspect, new, types

from compiler import walk, parse
from compiler import syntax, visitor, pycodegen, ast, misc
from compiler import consts, symbols, future

from defgen import waitForDeferred, deferredGenerator

class MungeNames(visitor.ASTVisitor):
    def __init__(self, which):
        visitor.ASTVisitor.__init__(self)
        self.whichNames = which

    def visitName(self, node):
        if node.name in self.whichNames:
            node.name = '__macro_special_' + node.name
    visitAssName = visitName

class MungeReturn(visitor.ASTVisitor):
    def visitReturn(self, node):
        ass = ast.AssName('__macro_return', 'OP_ASSIGN')
        new = ast.Assign([ass], node.value)

        node.__class__ = new.__class__
        node.__dict__ = new.__dict__

class MacroExpander(object):

    def __init__(self, macros):
        self.macros = {}
        for (k, v) in macros.iteritems():
            source = inspect.getsource(v)
            macroAST = parse(source)

            func = macroAST.node.nodes[0]
            code = func.code
            body = code.nodes

            # Now replace all the argument name looks up with munged
            # name lookups.
            mn = MungeNames(func.argnames)
            walk(code, mn)

            # Replace return with a munged assignment so we can steal
            # the value!
            mr = MungeReturn()
            walk(code, mr)

            self.macros[k] = (func.argnames, body)

    def default(self, node):
        for k in dir(node):
            v = getattr(node, k)
            if isinstance(v, ast.Node):
                r = self.dispatch(v)
                if isinstance(r, ast.Node):
                    node[k] = r
            elif isinstance(v, list):
                for i, c in enumerate(v):
                    r = self.dispatch(c)
                    if isinstance(r, ast.Node):
                        v[i] = r
                    elif isinstance(r, list):
                        v[i:i+1] = r

    def walk(self, ast):
        self.dispatch(ast)

    def dispatch(self, node):
        klass = node.__class__
        className = klass.__name__
        meth = getattr(self, 'visit' + className, self.default)
        return meth(node)

    def _setupNamespace(self, callFunc, names):
        if len(callFunc.args) != len(names):
            raise TypeError("Macro called with wrong number of arguments")
        r = []
        for (aExpr, aName) in zip(callFunc.args, names):
            name = '__macro_special_' + aName
            ass = ast.AssName(name, 'OP_ASSIGN')
            r.append(ast.Assign([ass], aExpr))
        return r

    def visitRaise(self, node):
        stmts = []
        for n in ('expr1', 'expr2', 'expr3'):
            e = getattr(node, n)
            if isinstance(e, ast.CallFunc):
                replacement = self.macros.get(e.node.name)
                if replacement is not None:
                    macroArguments, macroStatements = replacement
                    # Pass the arguments into macro-land
                    stmts.extend(self._setupNamespace(e, macroArguments))

                    # Insert the body of the macro
                    stmts.extend(macroStatements)

                    # Save the return value in a uniquely named variable
                    ass = ast.AssName('__macro_return_' + n, 'OP_ASSIGN')
                    saveret = ast.Assign([ass], ast.Name('__macro_return'))
                    stmts.append(saveret)

                    # Delete the commonly named macro return variable
                    delret = ast.AssName('__macro_return', 'OP_DELETE')
                    stmts.append(delret)

                    # Set the expression of the raise to load the saved name
                    setattr(node, n, ast.Name('__macro_return_' + n))
            else:
                pass
        if stmts:
            stmts.append(node)
            return stmts

    def visitPrint(self, node):
        stmts = []
        nodes = []
        for i, n in enumerate(node.nodes):
            if isinstance(n, ast.CallFunc):
                replacement = self.macros.get(n.node.name)
                if replacement is not None:
                    macroArguments, macroStatements = replacement

                    # Pass the arguments into macro-land
                    stmts.extend(self._setupNamespace(e, macroArguments))

                    # Insert the body of the macro
                    stmts.extend(macroStatements)

                    # Save the return value in a uniquely named variable
                    ass = ast.AssName('__macro_return_' + str(i), 'OP_ASSIGN')
                    saveret = ast.Assign([ass], ast.Name('__macro_return'))
                    stmts.append(saveret)

                    # Delete the commonly named macro return variable
                    delret = ast.AssName('__macro_return', 'OP_DELETE')
                    stmts.append(delret)

                    nodes.append(ast.Name('__macro_return_' + str(i)))
                else:
                    nodes.append(n)
                    self.dispatch(n)
            else:
                nodes.append(n)
                self.dispatch(n)
        if stmts:
            pass

    def expand(self, f):
        filename = inspect.getsourcefile(f)
        source = file(filename).read()

        ast = parse(source)

        self.walk(ast)

        misc.set_filename(filename, ast)
        syntax.check(ast)

        from ast_pp import SourceWriter
        sw = SourceWriter()
        self.walk(ast)

        gen = pycodegen.ModuleCodeGenerator(ast)
        gen.graph.setFlag(consts.CO_GENERATOR_ALLOWED)
        code = gen.getCode()

        # print ast.node.nodes[10]

        d = {}
        exec code in d
        return deferredGenerator(d.get(f.func_name))

from twisted.internet import reactor, defer

def wait(d):
    d = waitForDeferred(d)
    yield d
    d = d.getResult()
    __macro_return = d

def async(v):
    d = defer.Deferred()
    reactor.callLater(2, d.callback, v)
    return d

def testRaise():
    try:
        raise wait(async(Exception("Foo!")))
    except:
        cls, ins, tb = sys.exc_info()
        assert cls is Exception, "Wrong exception class"
        assert ins.args == ("Foo!",), "Wrong exception args"
    else:
        assert False, "No exception raised"

    print 'testRaise passed!'

def testAssignment():
    x = object()
    y = wait(async(x))
    assert x is y, "wrong object returned"

    print 'testAssignment passed!'

def testExpression():
    L = []
    def testcall(o):
        L.append(o)
    testcall(wait(async("Hello, world!")))
    assert L == ["Hello, world!"]

    print 'testExpression passed!'

def noise():
    reactor.callLater(0.5, noise)
    print 'NOISE'

def main():
    me = MacroExpander({'wait': wait})
    i = 1.0
    for f in testRaise, testAssignment, testExpression:
        f = me.expand(f)
        reactor.callLater(i, f)
        i += 0.2

    noise()
    reactor.callLater(1, f)
    reactor.run()

if __name__ == '__main__':
    main()

