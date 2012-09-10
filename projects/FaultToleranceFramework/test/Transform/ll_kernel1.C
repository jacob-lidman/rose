#include "Values.h"
#include <stdio.h>

int kernel(Values *val) {
    /*
     *******************************************************************
     *   Kernel 1 -- hydro fragment
     *******************************************************************
     *       DO 1 L = 1,Loop
     *       DO 1 k = 1,n
     *  1       X(k)= Q + Y(k)*(R*ZX(k+10) + T*ZX(k+11))
     */
    double *x = val->x, *y = val->y, *z = val->z;
    double Q = val->Q, R = val->R, T = val->T;
    long l,k, loop = 1, n = val->N * val->SCALE;
    #pragma resiliency
    for ( l=1 ; l<=loop ; l++ ) {
        for ( k=0 ; k<n-11 ; k++ ) {
            x[k] = Q + y[k]*( R*z[k+10] + T*z[k+11] );
        }
    }

    return 0;
}
