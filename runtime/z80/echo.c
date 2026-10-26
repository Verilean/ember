/* Byte echo without any Ember code: the interrupt and ring test of a new
 * target (plan M4z.2). */
#include "ember_rt.h"

extern const char *const drop_names[];
extern const unsigned drop_names_count;
extern const char *const note_names[];
extern const unsigned note_names_count;
const char *const drop_names[] = {""};
const unsigned drop_names_count = 0;
const char *const note_names[] = {""};
const unsigned note_names_count = 0;

void entry(void) {
  uint16_t v = ember_input_next();
  if (v < 0x100u) ember_out_byte((uint8_t)v);
}
