struct pair {
  unsigned int first;
  unsigned int second;
};

struct nested {
  struct pair first;
  struct pair second;
};

struct array_member {
  unsigned int values[2];
};

struct pair_array {
  struct pair values[2];
};

struct pointer_member {
  unsigned int *pointer;
  unsigned int value;
};

struct padded {
  unsigned char tag;
  unsigned int value;
};

void copy_pointer(struct pair *destination, struct pair *source) {
  *destination = *source;
}

unsigned int copy_local(struct pair *source) {
  struct pair destination;
  destination = *source;
  return destination.first + destination.second;
}

void copy_nested(struct nested *destination, struct nested *source) {
  destination->first = source->second;
}

void copy_array_member(struct array_member *destination,
                       struct array_member *source) {
  *destination = *source;
}

void copy_pointer_member(struct pointer_member *destination,
                         struct pointer_member *source) {
  *destination = *source;
}

void copy_padding(struct padded *destination, struct padded *source) {
  *destination = *source;
}

void copy_partial(struct pair *destination, struct pair *source) {
  *destination = *source;
}

void copy_self(struct pair *object) {
  *object = *object;
}

void copy_fields(struct nested *object) {
  object->first = object->second;
}

void copy_field_self(struct nested *object) {
  object->first = object->first;
}

void copy_array_fields(struct pair_array *destination, struct pair_array *source) {
  destination->values[0] = source->values[1];
}

void copy_qualified(struct pair *destination, volatile struct pair *source) {
  *destination = *source;
}
