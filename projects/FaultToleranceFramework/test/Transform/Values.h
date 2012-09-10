#ifndef VALUES_HDR
#define VALUES_HDR

#include <stdio.h>
#include <string.h>
#include <functional>
#include <iostream>

using namespace std;

struct Values {
     //Sizes...
       unsigned long SCALE, N, Nsmall;
     //Registers
          double *x, *y, *z, *v, *w, *u, *du1, *du2, *du3;
          //double b[64][64], px[101][25], cx[101][25];
          //double u1[2][101][5], u2[2][101][5], u3[2][101][5];
          double Q, R, T, Dm22, Dm23, Dm24, Dm25, Dm26, Dm27, Dm28, Ar, Br, C0, Cr,
                Sig, A11, A12, A13, A21, A22, A23, A31, A32, A33;

     size_t getSize() {
          return (6*sizeof(double)*(N*(1+SCALE)) + sizeof(Values));
     }

     Values(const Values *val)  {
          this->N = val->N;
          this->Nsmall = val->Nsmall;
          this->SCALE = val->SCALE;

          if((this->x = new (nothrow) double[N*(1+SCALE)]) != 0)
             memcpy(x, val->x, N*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << N*(1+SCALE) << ") to X..." << endl;
          if((this->y = new (nothrow) double[N*(1+SCALE)]) != 0)
             memcpy(y, val->y, N*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << N*(1+SCALE) << ") to Y..." << endl;
          if((this->z = new (nothrow) double[N*(1+SCALE)]) != 0)
             memcpy(z, val->z, N*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << N*(1+SCALE) << ") to Z..." << endl;
          /*if((this->v = new (nothrow) double[N*(1+SCALE)]) != 0)
             memcpy(v, val->v, N*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << N*(1+SCALE) << ") to V..." << endl;
          if((this->w = new (nothrow) double[N*(1+SCALE)]) != 0)
             memcpy(w, val->w, N*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << N*(1+SCALE) << ") to W..." << endl;
          if((this->u = new (nothrow) double[N*(1+SCALE)]) != 0)
             memcpy(u, val->u, N*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << N*(1+SCALE) << ") to U..." << endl;

          if((this->du1 = new (nothrow) double[Nsmall*(1+SCALE)]) != 0)
             memcpy(du1, val->du1, Nsmall*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << Nsmall*(1+SCALE) << ") to DU1..." << endl;
          if((this->du2 = new (nothrow) double[Nsmall*(1+SCALE)]) != 0)
             memcpy(du2, val->du1, Nsmall*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << Nsmall*(1+SCALE) << ") to DU2..." << endl;
          if((this->du3 = new (nothrow) double[Nsmall*(1+SCALE)]) != 0)
             memcpy(du1, val->du3, Nsmall*(1+SCALE));
          else
               cout << "Unable to allocate memory (" << Nsmall*(1+SCALE) << ") to DU3..." << endl;*/
     }
     Values(long N, long Nsmall, long SCALE) {
          this->N = N;
          this->Nsmall = Nsmall;
          this->SCALE = SCALE;

          x = new double[N*(1+SCALE)];
          y = new double[N*(1+SCALE)];
          z = new double[N*(1+SCALE)];
          //v = new double[N*(1+SCALE)];
          //w = new double[N*(1+SCALE)];
          //u = new double[N*(1+SCALE)];

          //du1 = new double[Nsmall*(1+SCALE)];   
          //du2 = new double[Nsmall*(1+SCALE)]; 
          //du3 = new double[Nsmall*(1+SCALE)];
     };
     ~Values() {
          delete x;
          delete y;
          delete z;
          //delete v;
          //delete w;
          //delete u;
          //delete du1;
          //delete du2;
          //delete du3;
     }
          
};

struct ValueComp : std::binary_function<Values *, Values *, bool> {
  bool operator() (const Values *x, const Values *y) const {
     if(x == NULL || y == NULL)
        return false;
     //Compare output to correct output
       return ( (memcmp(x->x, y->x, x->N * (1+x->SCALE)*sizeof(double)) == 0) &&
	           (memcmp(x->y, y->y, x->N * (1+x->SCALE)*sizeof(double)) == 0) &&
                (memcmp(x->z, y->z, x->N * (1+x->SCALE)*sizeof(double)) == 0) );
       	      //(memcmp(x->v, y->v, x->N * (1+x->SCALE)*sizeof(double)) == 0) &&
                //(memcmp(x->w, y->w, x->N * (1+x->SCALE)*sizeof(double)) == 0) &&
                //(memcmp(x->u, y->u, x->N * (1+x->SCALE)*sizeof(double)) == 0));
  }
};

#endif

