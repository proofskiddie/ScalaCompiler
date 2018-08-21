// A PCG random number generator. (Specifically, this is the variant
// called XSH RR in the paper, with a 16-bit state and 8-bit output).
// See http://www.pcg-random.org/

def makeRNG(seed: Int) = {
  val rng = new Array[Int](1);
  rng(0) = seed & 0xFFFF;
  rng
};

def rngGetState(rng: Array[Int]) = rng(0);

def rngSetState(rng: Array[Int], state: Int) = rng(0) = state & 0xFFFF;

def rngRotateRight8(x: Int, y: Int) =
  ((x >> y) | (x << (8 - y))) & 0xFF;

def rngStep(rng: Array[Int]) =
  rngSetState(rng, rngGetState(rng) * 12829 + 47989);

def rngOutput(rng: Array[Int]) = {
  val state = rngGetState(rng);
  rngRotateRight8(0xFF & ((state ^ (state >> 5)) >> 5), state >> 13)
};

// Return the next 8-bit unsigned integer (0 to 255, included)
def rngNextInt8(rng: Array[Int]) = {
  val i = rngOutput(rng);
  rngStep(rng);
  i
};

// FIXME: this is hackish, find a better way to do it (probably using
// multiple streams, see sample/pcg32x2-demo.c in the PCG source).
def rngNextInt(rng: Array[Int]) = {
  val b0 = rngNextInt8(rng);
  val b1 = rngNextInt8(rng);
  val b2 = rngNextInt8(rng);
  val b3 = rngNextInt8(rng);
  (b0 << 24) | (b1 << 16) | (b2 << 8) | b3
};
