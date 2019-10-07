abstract class Rexp
case object ZERO extends Rexp          
case object ONE extends Rexp                   
case class CHAR(c: Char) extends Rexp          
case class ALT(r1: Rexp, r2: Rexp) extends Rexp  
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp  
case class STAR(r: Rexp) extends Rexp     
case class RANGE(s: Set[Char]) extends Rexp // DONE
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class UPTO(r: Rexp, m: Int) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOT(r: Rexp) extends Rexp 
case class CFUN(f: Char => Boolean) extends Rexp

def nullable(r: Rexp) : Boolean = r match {
  case ZERO             => false
  case ONE              => true
  case CHAR(_)          => false
  case ALT(r1, r2)      => nullable(r1) || nullable(r2)
  case SEQ(r1, r2)      => nullable(r1) && nullable(r2)
  case STAR(_)          => true
  case RANGE(s)         => false
  case PLUS(r)          => nullable(r)
  case OPTIONAL(r)      => true
  case NTIMES(r, i)     => if (i == 0) true else nullable(r)
  case UPTO(r, _)       => true
  case FROM(r, i)       => if (i == 0) true else nullable(r)
  case BETWEEN(r, i, _) => if (i == 0) true else nullable(r)
  case NOT(r)           => !nullable(r) 
}

/* Nullable Test Cases */
nullable(ZERO) == false
nullable(ONE) == true
nullable(CHAR('a')) == false
nullable(ALT(CHAR('a'), CHAR('b'))) == false
nullable(ALT(ONE, CHAR('a'))) == true
nullable(ALT(ZERO, CHAR('b'))) == false
nullable(ALT(SEQ(CHAR('a'), CHAR('b')), CHAR('a'))) == false
nullable(ALT(ALT(CHAR('a'), ONE), CHAR('a'))) == true
nullable(STAR(CHAR('a'))) == true
nullable(STAR(SEQ(CHAR('a'), CHAR('b'))))


def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO             => ZERO
  case ONE              => ZERO
  case CHAR(d)          => if (c == d) ONE else ZERO
  case ALT(r1, r2)      => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2)      => if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2)) else SEQ(der(c, r1), r2)
  case STAR(r1)         => SEQ(der(c, r1), STAR(r1))
  case RANGE(s)         => if (s.contains(c)) ONE else ZERO
  case PLUS(r)          => SEQ(der(c, r), STAR(r)) // Ok
  case OPTIONAL(r)      => ALT(ONE, der(c, r)) //Ok
  case NTIMES(r, i)     => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))  //Ok
  case FROM(r, i)       => if (i == 0) FROM(r, i) else SEQ(der(c, r), FROM(r, i - 1)) // BROKEN
  case UPTO(r, i)       => if (i == 0) ZERO else SEQ(der(c, r), UPTO(r, i - 1)) //Ok
  case BETWEEN(r, i, j) => if (i == 0) SEQ(der(c, r), UPTO(r, j - 1)) else SEQ(der(c, r), BETWEEN(r, i - 1, j - 1))
  case NOT(r)           => NOT(der(c, r))
}

simp(der('a', BETWEEN(SEQ(CHAR('a'), CHAR('b')), 2, 3)))
simp(der('b', BETWEEN(SEQ(CHAR('a'), CHAR('b')), 2, 3)))
simp(der('a', BETWEEN(SEQ(CHAR('a'), CHAR('b')), 0, 2)))

simp(der('a', PLUS(CHAR('a'))))
simp(der('a', PLUS(SEQ(CHAR('a'), CHAR('b')))))
simp(der('b', PLUS(SEQ(CHAR('a'), CHAR('b'))))) 
simp(der('a', PLUS(ALT(CHAR('a'), CHAR('b')))))
simp(der('b', PLUS(ALT(CHAR('a'), CHAR('b')))))
simp(der('b', PLUS(RANGE(Set('a', 'b', 'c')))))

simp(der('a', OPTIONAL(CHAR('a'))))
simp(der('b', OPTIONAL(CHAR('a'))))
simp(der('a', OPTIONAL(SEQ(CHAR('a'), CHAR('b')))))
simp(der('b', OPTIONAL(SEQ(CHAR('a'), CHAR('b')))))
simp(der('a', OPTIONAL(ALT(CHAR('a'), CHAR('b')))))
simp(der('a', OPTIONAL(ZERO)))
simp(der('a', NTIMES(OPTIONAL(CHAR('a')), 3)))

/* Derivative Test Cases */
der('a', SEQ(CHAR('c'), CHAR('b')))

der('a', RANGE(Set('a', 'b', 'c')))
der('d', RANGE(Set('a', 'b', 'c')))
der('d', RANGE(Set()))

der('a', PLUS(CHAR('a')))
der('a', PLUS(SEQ(CHAR('a'), CHAR('b')))) 
der('b', PLUS(SEQ(CHAR('a'), CHAR('b')))) 

der('a', OPTIONAL(CHAR('a')))
der('b', OPTIONAL(CHAR('a')))
der('a', OPTIONAL(SEQ(CHAR('a'), CHAR('b'))))

der('a', NTIMES(OPTIONAL(CHAR('a')), 2))

der('a', FROM(CHAR('a'), 2))
der('a', FROM(CHAR('a'), 1))
der('a', FROM(CHAR('a'), 0))
der('b', FROM(CHAR('a'), 0))
der('a', FROM(SEQ(CHAR('a'), CHAR('b')), 2))
der('b', FROM(SEQ(CHAR('a'), CHAR('b')), 2))



der('b', FROM(SEQ(CHAR('a'), CHAR('b')), 1))

def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}



def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}

def matcher(r: Rexp, s: String) : Boolean = nullable(ders(s.toList, r))

/* Tests as given in Coursework Handout */
matcher(NTIMES(CHAR('a'), 3), "") == false
matcher(NTIMES(CHAR('a'), 3), "a") == false
matcher(NTIMES(CHAR('a'), 3), "aa") == false
matcher(NTIMES(CHAR('a'), 3), "aaa") == true
matcher(NTIMES(CHAR('a'), 3), "aaaa") == false
matcher(NTIMES(CHAR('a'), 3), "aaaaa") == false

matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "") == true
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "a") == true
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aa") == true
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aaa") == true 
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aaaa") == false
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aaaaa") == false

matcher(UPTO(CHAR('a'), 3), "") == true
matcher(UPTO(CHAR('a'), 3), "a") == true
matcher(UPTO(CHAR('a'), 3), "aa") == true
matcher(UPTO(CHAR('a'), 3), "aaa") == true
matcher(UPTO(CHAR('a'), 3), "aaaa") == false
matcher(UPTO(CHAR('a'), 3), "aaaaa") == false

matcher(UPTO(OPTIONAL(CHAR('a')), 3), "") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "a") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aa") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aaa") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aaaa") == false
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aaaaa") == false

matcher(BETWEEN(CHAR('a'), 3, 5), "") == false
matcher(BETWEEN(CHAR('a'), 3, 5), "a") == false
matcher(BETWEEN(CHAR('a'), 3, 5), "aa") == false
matcher(BETWEEN(CHAR('a'), 3, 5), "aaa") == true
matcher(BETWEEN(CHAR('a'), 3, 5), "aaaa") == true
matcher(BETWEEN(CHAR('a'), 3, 5), "aaaaa") == true

matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "a") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aa") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aaa") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aaaa") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aaaaa") == true


