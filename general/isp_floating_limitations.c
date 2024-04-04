/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Test for processing the index of an array."
*/

int X;
int XMAX;
double Y;
double YMAX;

/*@ requires \valid(&X);
    requires \valid(&XMAX);
    requires X >= 0 && X <= 30;
    requires XMAX == 30;

    requires \valid(&Y);
    requires \valid(&YMAX);
    requires Y >= 0.0 && Y <= 30.0;
    requires YMAX == 30.0;
    requires \is_finite(\div_double(Y, YMAX));
    requires \is_finite(\mul_double(\div_double(Y, YMAX), (double)100.0));
 */
void main() {
  int i = (X / XMAX) * 100;
  //@ assert i \in {0, 100};


  double j = (Y / YMAX) * 100.0;
  //@ assert j >= 0.0 && j <= 100.0;
}
