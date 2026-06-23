/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing bounds for mutated struct fields through pointer arguments."
*/

#include <limits.h>

int init1;
int init2;
int r1;
int r2;

typedef struct {
    int val;
} S;

void mod(S* t1, S* t2) {
    t1->val = t1->val + 1;
    t2->val = t2->val - 1;
}

/*@
  requires INT_MIN < init1 <= INT_MAX;
  requires INT_MIN < init2 <= INT_MAX;
  ensures r1 == init1+1;
  ensures r2 == init2-1;
*/
int main() {
    S s1 = {init1};
    S s2 = {init2};

    mod(&s1, &s2);

    r1 = s1.val;
    r2 = s2.val;

    return 0;
}
