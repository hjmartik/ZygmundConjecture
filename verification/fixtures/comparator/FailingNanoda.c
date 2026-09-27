/* Deliberate isolated checker fault, not a proof checker. Apache-2.0. */
#include <unistd.h>
int main(void) {
    static const char marker[] = "PACKAGING_FIXTURE_NANODA_FAILURE\n";
    (void)write(2, marker, sizeof(marker) - 1);
    return 23;
}
