//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: [](AP(a != 0) ==> <> AP(r!= 0));

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume();
extern int __VERIFIER_nondet_int();

a = 0;
r = 0;

int main() {
   int n;
  while(__VERIFIER_nondet_int()) {
    a = 1;
    a = 0;
    n = __VERIFIER_nondet_int();
    while(n>0) {
      n--;
    }
    r = 1;
    r = 0;
  }
  while(1) { int x; x=x; }
  return 0;
}
