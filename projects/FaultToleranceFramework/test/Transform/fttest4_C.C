/* C Test #4:
 *	- Handle stm:s with multiple side-effects
 *	- Handle trivial assignments
*/

#include<stdio.h>
#include<stdlib.h>

int main () {
     int a=1,b=2,g=7;
     #pragma resiliency
     {
          a = g*(b = a + 2);
	  b = 10;     
          a = 2*g;
     }
     printf ("result ========= %d : %d : %d\n", a,b,g);
}
