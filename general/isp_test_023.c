/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Function arguments, non-pointer."
COMMENT: "This test is failing. To solve the problem a mechanism 
          should be implemented to generate simmilar annotations
          to the commentd annotations in increment()."
*/

int X;

/*
    behavior manually_generated3:
      assumes \true;
      requires x ∈ {1, 2};
      ensures \result == \old(x) + 1;
      assigns \nothing;
 */
int increment(int x) {
  x += 1;
  return x;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires X == 1;
    ensures \result == 3;
    assigns \nothing;
    */
int main() {
  int temp = increment(X);
  temp = increment(temp);
  return temp;
}
