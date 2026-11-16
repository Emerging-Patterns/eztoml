# proofs of laws/BuildersMakeValues.bend
import Base
import ../laws/BuildersMakeValues.bend as Laws

# each builder is its constructor, so each law holds by unfolding
def Laws.str_makes_string(_text):
  {==}

def Laws.integer_makes_integer(_sign, _text):
  {==}

def Laws.float_makes_float(_sign, _text):
  {==}

def Laws.boolean_makes_boolean(_bit):
  {==}

def Laws.array_makes_array(_items):
  {==}

def Laws.inline_makes_inline(_rows):
  {==}

def Laws.table_makes_table(_path, _rows):
  {==}

def Laws.pair_makes_pair(_name, _val):
  {==}
