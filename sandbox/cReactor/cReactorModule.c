/*
 * Copyright (c) 2001-2004 Twisted Matrix Laboratories.
 * See LICENSE for details.

 * 
 */
/* cReactorModule.c - the cReactor extension module. */

/* includes */
#include "cReactor.h"
#include <stdio.h>
#include <signal.h>
#include <unistd.h>

/* Install the cReactor via main.installReactor(). */
static PyObject *
cReactorModule_install(PyObject *self, PyObject *args)
{
    PyObject *reactor;
    PyObject *module;
    PyObject *result;

    UNUSED(self);
   
    /* Arg check. */
    if (!PyArg_ParseTuple(args, ":install"))
    {
        return NULL;
    }

    /* Get the twisted.internet.main module. */
    module = cReactorUtil_FromImport("twisted.internet", "main");
    if (!module)
    {
        return NULL;
    }

    /* Create a new reactor. */
    reactor = cReactor_New();
    if (!reactor)
    {
        Py_DECREF(module);
        return NULL;
    }

    /* Call the installReactor method. */
    result = PyObject_CallMethod(module, "installReactor", "(O)", reactor);
    Py_DECREF(module);

    return result;
}


static PyObject *
cReactorModule_new(PyObject *self, PyObject *args)
{
    UNUSED(self);

    if (!PyArg_ParseTuple(args, ":new"))
    {
        return NULL;
    }

    return cReactor_New();
}


/* Module methods. */
static PyMethodDef cReactor_methods[] = 
{
    { "install",    cReactorModule_install,     METH_VARARGS, "Install the cReactor." },
    { "new",        cReactorModule_new,         METH_VARARGS, "" },

    { NULL, NULL, METH_VARARGS, NULL },
};

/* Required init function to be an extension module. */
DL_EXPORT(void)
initcReactor(void)
{
    if (getenv("CREACTOR_DEBUG") != NULL)
    {
        kill(0, SIGTRAP);
    }
    cDelayedCall_init();
    cReactorTCP_init();

    Py_InitModule3("cReactor", cReactor_methods, "The Twisted C Reactor.");
}

/* vim: set sts=4 sw=4: */
