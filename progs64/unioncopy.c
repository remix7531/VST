union choice {
  unsigned int integer;
  unsigned int *pointer;
};

union padded_choice {
  unsigned char tiny;
  unsigned int full;
};

union nested_choice {
  union choice inner;
  unsigned int integer;
};

struct union_fields {
  union choice first;
  union choice second;
};

struct union_array {
  union choice values[2];
};

struct union_pair {
  unsigned int first;
  unsigned int second;
};

union pair_choice {
  struct union_pair pair;
  unsigned int integer;
};

void copy_choice(union choice *destination, union choice *source) {
  *destination = *source;
}

void copy_padded_choice(union padded_choice *destination,
                        union padded_choice *source) {
  *destination = *source;
}

void copy_nested_choice(union nested_choice *destination,
                        union nested_choice *source) {
  *destination = *source;
}

void copy_union_fields_whole(struct union_fields *destination,
                             struct union_fields *source) {
  *destination = *source;
}

void copy_union_array_whole(struct union_array *destination,
                            struct union_array *source) {
  *destination = *source;
}

void copy_choice_self(union choice *object) {
  *object = *object;
}

void copy_union_fields(struct union_fields *destination,
                       struct union_fields *source) {
  destination->first = source->second;
}

void copy_union_siblings(struct union_fields *object) {
  object->first = object->second;
}

void copy_union_field_self(struct union_fields *object) {
  object->first = object->first;
}

void copy_union_array_fields(struct union_array *destination,
                             struct union_array *source) {
  destination->values[0] = source->values[1];
}

void copy_union_pair(union pair_choice *destination,
                     union pair_choice *source) {
  destination->pair = source->pair;
}
