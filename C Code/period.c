#include <stdio.h>
#include <string.h>


/*@ 
    requires l >= 0;
    requires \valid(x+(0..(l-1)));
    requires p >= 0;

    behavior zero:
        assumes p == 0;
        ensures \result = 1;

    behavior one: 
        assumes p > 0;
        ensures \forall int i; 0 <= i < l-p-1; x[i] == x[i+p]

    complete behaviors one,zero;
    disjoint behaviors one,zero;
*/

unsigned has_period(char x[], int p, unsigned l) {
    if (p == l) return 1;
    if ((l % p) != 0) return 0;

        /*@
            loop assigns i;
        */
        for (int i = 0 ; i < l-p-1 ; ++i) {
            if (x[i] == x[i + p])
                return 1;
        }

    return 0;
}

/*@
    requires l >= 0;
    requires \valid(x+(0..l-1));
    
    ensures 0 < \result <= l;
*/

unsigned per(char x[], unsigned l) {
    int p = 1;
    /*@
        loop assigns p;
    */
    while (p <= l && !has_period(x, p, l))
        ++p;
    return p;
}
