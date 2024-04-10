/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Test for processing the index of an array."
*/

int DB[5];

typedef enum { RPM, SPEED, TEMPERATURE, HUMIDITY, PRESSURE } PARAMETER;

PARAMETER X;

int read_db(PARAMETER p) {
  return DB[p];
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(DB+(0..4));
    requires DB[RPM] ∈ (0..9000);
    requires DB[SPEED] ∈ (0..400);
    requires DB[TEMPERATURE] ∈ (0..400);
    requires DB[HUMIDITY] ∈ (0..100);
    requires DB[PRESSURE] ∈ (0..150);
    requires X ∈ {RPM, SPEED, PRESSURE};
    assigns \nothing;
    */
void main() {
      read_db(X);
}
