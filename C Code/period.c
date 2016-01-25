//////////////////////////////////////////////////////////////////
//                          SEMANTICS                          //
//////////////////////////////////////////////////////////////////
/* Given a not-empty string x.  An integer number p such that
0 < p ≤|x| is meant to be "a period of x" if

  x[i] = x[i + p]

for i = 0, 1, ... , |x| − p − 1.
Note that, for each not-empty string, the length of the string
is a period of itself.  In this way, every not-empty string
has got at least one period.  So is well formed the concept of minimum
period of string x, denoted by per(x):

  per(x) = min { p | p is period of x }.

Write a C function

   unsigned per(const char x[], unsigned l)

that, given a string x of length l, returns per(x). */
//////////////////////////////////////////////////////////////////

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