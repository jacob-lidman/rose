#include "Values.h"
#include <stdio.h>

//Change to kernel:
//	* "loop = 1" -> "loop = 1+6"
//	* "for ( k=6 ; k<loop ; k=k+m ) {" -> "for ( k=6 ; k<loop ; k=k+m+1 ) {"

int kernel(Values *val) {
    /*
     *******************************************************************
     *   Kernel 4 -- banded linear equations
     *******************************************************************
     *            m= (1001-7)/2
     *    DO 444  L= 1,Loop
     *    DO 444  k= 7,1001,m
     *           lw= k-6
     *         temp= X(k-1)
     CDIR$ IVDEP
     *    DO   4  j= 5,n,5
     *       temp  = temp   - XZ(lw)*Y(j)
     *  4        lw= lw+1
     *       X(k-1)= Y(5)*temp
     *444 CONTINUE
     */
    double *x = val->x, *y = val->y, temp;
    long l,k, lw, j, m, loop = 1+6, n = val->N * val->SCALE;
    #pragma resiliency
    {
    m = ( loop-7 )/2;
    for ( l=1 ; l<=loop ; l++ ) {
        for ( k=6 ; k<loop ; k=k+m+1 ) {
            lw = k - 6;
            temp = x[k-1];
            for ( j=4 ; j<n ; j=j+5 ) {
                temp -= x[lw]*y[j];
                lw++;
            }
            x[k-1] = y[4]*temp;
        }
    }
    }
    return 0;
}

