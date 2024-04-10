/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing interface specifications detection."
*/

int X;

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires X \in (5..10);
    ensures \result \in (5..10);
    assigns \nothing;
    */
int main() {
  return X;
}
