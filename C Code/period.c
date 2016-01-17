#include <stdio.h>
#include <string.h>


/*@ 
    requires l >= 0;
    requires \valid(x+(0..(l-1)));

*/

unsigned has_period(char x[], int p, unsigned l) {
    if (p == l) return 1;
    if ((l % p) != 0) return 0;

        for (int i = 0 ; i < l - p - 1 ; ++i) {
            if (x[i] != x[i + p])
                return 0;
        }

    return 1;
}

/*@
    requires l >= 0;
    requires \valid(x+(0..(l-1)));

    ensures 0 < \result <= l;
*/

unsigned per(char x[], unsigned l) {
    int p = 1;
    while (p <= l && !has_period(x, p, l))
        ++p;
    return p;
}
