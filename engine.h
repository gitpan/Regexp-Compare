#ifndef engine_h
#define engine_h

#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#if PERL_API_REVISION != 5
#error This module is only for Perl 5
#else
#if PERL_API_VERSION == 12
#else
#if PERL_API_VERSION == 14
#define RC_DEFAULT_UNICODE
#define ANYOF_UNICODE 0
#else
#if PERL_API_VERSION == 16
#define RC_DEFAULT_UNICODE
#define RC_INVLIST
#define ANYOF_UNICODE 0
#else
#error Unsupported PERL_API_VERSION
#endif
#endif
#endif
#endif

/* Set on error (i.e. failed memory allocation, unexpected regexp
   construct), used by the XS glue as an argument to croak. Value
   isn't freed - it must be a literal string. */
extern char *rc_error;

/* Initializes module tables. Doesn't fail, must be called before any
   other function below. */
void rc_init();

/* might croak but never returns null */
REGEXP *rc_regcomp(SV *rs);

void rc_regfree(REGEXP *rx);

int rc_compare(REGEXP *pt1, REGEXP *pt2);

#endif
