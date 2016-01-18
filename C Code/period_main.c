#include <stdio.h>
#include <string.h>

unsigned has_period(char x[], int p, unsigned l) {
    if (p == l) return 1;
    if ((l % p) != 0) return 0;

        for (int i = 0 ; i < l - p - 1 ; ++i) {
            if (x[i] != x[i + p])
                return 0;
        }

    return 1;
}

unsigned per(char x[], unsigned l) {
    int p = 1;
    /* while (p <= l && !has_period(x, p, l))
        ++p;
    return p;
    */
     for(int p = 1; p<=l; ++p) {
        if(has_period(x,p,l))
            return p;
    }
}

int main() {

	char x[32];

	printf("Insert a string: '%s' ",x);

	do {
        scanf("%s", x);
    } while (x[0] == '\0');

	printf("Minimun period of'%s' is %d\n", x,per(x,strlen(x)));

	return 0;
}
