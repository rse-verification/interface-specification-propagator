/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing if statements."
*/

int X;
int Y;
int Z;

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(&Z);
    requires \valid(&Z);
    requires X ∈ {3, 4, 5};
    ensures Z ∈ {6, 8, 10};
    assigns Z;
    */
void main() {
  if (X < 3)
    Y = X;
  else
    Z = 2 * X;
}
