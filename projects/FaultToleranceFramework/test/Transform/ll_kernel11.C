#include "Values.h"
#include <stdio.h>

int kernel(Values *val) {
    /*
     *******************************************************************
     *   Kernel 11 -- first sum
     *******************************************************************
     *    DO 11 L = 1,Loop
     *        X(1)= Y(1)
     *    DO 11 k = 2,n
     * 11     X(k)= X(k-1) + Y(k)
     */
    double *x = val->x, *y = val->y;
    long l,k, loop = 1, n = val->N * val->SCALE;
    #pragma resiliency
    for ( l=1 ; l<=loop ; l++ ) {
        x[0] = y[0];
        for ( k=1 ; k<n ; k++ ) {
            x[k] = x[k-1] + y[k];
        }
    }

    return 0;
}

