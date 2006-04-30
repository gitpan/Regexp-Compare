#ifndef engine_h
#define engine_h

#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

extern char *rc_error;

void rc_init();

regexp *rc_regcomp(char *rs);

int rc_compare(regnode *p1, regnode *p2);

#endif
