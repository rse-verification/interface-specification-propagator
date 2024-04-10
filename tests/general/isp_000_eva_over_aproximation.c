/* run.config
OPT: -autoload-plugins -isp -isp-print -isp-entry-point calculate
COMMENT: "Show over approximation of EVA. Given the requirements, calculate() will never return a value less than 0 but EVA evaluates its result to be between -10 and 10."
*/

int X;
int Y;

/*@ requires \valid_read(&Y);
    requires \valid_read(&X);
    requires X \in (0..10);
    requires Y \in (0..20);
 */
int calculate() {
  if (Y > X)
    return 0;
  else
    return X - Y;
}