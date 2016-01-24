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
    requires l > 0;
    requires p >= 0;
    
    behavior zero:
      assumes  p == l;
      ensures \result == 1;
    
    behavior one: 
      assumes l != p && (l%p) == 0;
      assumes \forall int i; 0 <= i < l-p-1 ==> x[i] == x[i+p];
      ensures \result == 1;
  
    behavior two:
      assumes l != p && (l%p) == 0;
      assumes !(\forall int i; 0 <= i < l-p-1 ==> x[i] == x[i+p]);
      ensures \result == 0;

    behavior three:
      assumes p != l && l%p != 0;
      ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/

unsigned has_period(const char x[], unsigned int p, unsigned l) {
    if (p == l) return 1;
    if ((l % p) != 0) return 0;
        /*@
            loop assigns i;

            loop invariant \forall int j; 0 <= j < i ==> (x[j] == x[j+p]);
            loop invariant i <= l-p-1;
            loop invariant i >= 0;
        */
        
        for (int i = 0 ; i < l-p-1 ; ++i) {
            if (x[i] != x[i + p])
                return 0;
        }     
       
    return 1; 
}

/*@
   predicate has_period(char* x, unsigned int p, unsigned l) =
      \forall int i; i <= (l-p-1) ==>  x[i] == x[i+p];
*/

/*@
    requires l > 0;
    requires \valid(x+(0..l-1));
    
    ensures 0 < \result <= l;
*/

unsigned per(const char x[], unsigned l) {
     int p = 1;

    /*@
        loop invariant 0 < p <= l;
    */

    while(p <= l && !has_period(x,p,l)) 
        ++p;

    return 1;
}
