/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Global variables used in caluculating returned values."
*/

int X;

int incremented_x() {
  int x = X + 1;
  return x;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires X == 1;
    ensures \result == 2;
    assigns \nothing;
    */
int main() {
  int temp = incremented_x();
  return temp;
}
