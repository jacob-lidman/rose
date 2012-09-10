#include "Values.h"
#include <stdio.h>

int kernel(Values *val) {
    /*
     *******************************************************************
     *   Kernel 5 -- tri-diagonal elimination, below diagonal
     *******************************************************************
     *    DO 5 L = 1,Loop
     *    DO 5 i = 2,n
     *  5    X(i)= Z(i)*(Y(i) - X(i-1))
     */
     double *x = val->x, *y = val->y, *z = val->z;
    long l,i, loop = 1, n = val->N * val->SCALE;
    #pragma resiliency
    for ( l=1 ; l<=loop ; l++ ) {
        for ( i=1 ; i<n ; i++ ) {
            x[i] = z[i]*( y[i] - x[i-1] );
        }
    }

    return 0;
}

