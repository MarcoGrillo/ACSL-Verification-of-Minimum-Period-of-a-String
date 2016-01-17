//////////////////////////////////////////////////////////////////
//                          SEMANTICA                           //
//////////////////////////////////////////////////////////////////
/* Sia x una stringa non vuota.  Un intero p tale che
0 < p ≤|x| si dice essere "un periodo di x" se

  x[i] = x[i + p]

per i = 0, 1, ... , |x| − p − 1.
Si noti che, per ogni stringa non vuota, la lunghezza della stringa
è un periodo della medesima.  In tal modo, ogni stringa non vuota
ha almeno un periodo.  E' quindi ben definito il concetto di minimo
periodo di una stringa x, denotato da per(x):

  per(x) = min { p | p è un periodo di x }.

Scriva una funzione C

   unsigned per(const char x[], unsigned l)

che data una stringa x di lunghezza l restituisce per(x). */
//////////////////////////////////////////////////////////////////


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
