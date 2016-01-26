#include <stdio.h>
#include <string.h>

/*@
   predicate is_periodic(char* x, unsigned int p, unsigned int l) =
      (\forall unsigned int i; 0 <= i < (l-p-1) ==>  x[i] == x[i+p]) && (l%p == 0) || (p == l);
*/

/*@ 
    requires \valid(x+(0..l-1));
    requires l > 0;
    requires p > 0;
    
    assigns \nothing;

    ensures is_periodic(x,p,l) ==> \result == 1;
    ensures !is_periodic(x,p,l) ==> \result == 0;
*/

unsigned has_period(const char x[], unsigned int p, unsigned l) {

    if (p == l) return 1;
    if ((l % p) != 0) return 0;
        /*@
            loop assigns i;

            loop invariant \forall unsigned int j; 0 <= j < i ==> (x[j] == x[j+p]);
            loop invariant i <= l-p-1;
            loop invariant i >= 0;
        */
        
        for (unsigned i = 0 ; i < l-p-1 ; ++i) {
            if (x[i] != x[i + p])
                return 0;
        }     
       
    return 1; 
}

/*@
    requires \valid(x+(0..l-1));
    requires l > 0;

    ensures 1 <= \result <= l;
    ensures is_periodic(x,\result,l);    
    ensures \forall unsigned int p; 0 < p < \result ==> !is_periodic(x,p,l);                      
*/

unsigned per(const char x[], unsigned l) {
    unsigned int p;
    /*@
        loop assigns p;
        loop invariant p >= 1;
        loop invariant p <= l;
        loop invariant \forall unsigned int i; 0 < i < p ==> !is_periodic(x,i,l);
        loop variant l-p;
    */

    for(p = 1; p < l; ++p) {
        if(has_period(x,p,l))
            return p;
    }

    return p;
}


int main() {

	const char x1[] = {"abcabcabc"};
    const char x2[] = {"0101010101010101"};
    const char x3[] = {"abcabcdefgh"};
    const char x4[] = {"oh oh oh"};
    const char x5[] = {"periodo"};
    const char x6[] = {"tramtram"};
    const char x7[] = {"stoppots"};
    const char x8[] = {"test main"};
    const char x9[] = {"333444333444"};
    const char x10[] = {"bobo"};
    const char x11[] = {"marcomarcomarcomarco"};
    const char x12[] = {"123456789123456789123456789"};


	printf("'%s' = %d\n",x1,per(x1,strlen(x1)));
    printf("'%s' = %d\n",x2,per(x2,strlen(x2)));
    printf("'%s' = %d\n",x3,per(x3,strlen(x3)));
    printf("'%s' = %d\n",x4,per(x4,strlen(x4)));
    printf("'%s' = %d\n",x5,per(x5,strlen(x5)));
    printf("'%s' = %d\n",x6,per(x6,strlen(x6)));
    printf("'%s' = %d\n",x7,per(x7,strlen(x7)));
    printf("'%s' = %d\n",x8,per(x8,strlen(x8)));
    printf("'%s' = %d\n",x9,per(x9,strlen(x9)));
    printf("'%s' = %d\n",x10,per(x10,strlen(x10)));
    printf("'%s' = %d\n",x11,per(x11,strlen(x11)));
    printf("'%s' = %d\n",x12,per(x12,strlen(x12)));

	return 0;
}