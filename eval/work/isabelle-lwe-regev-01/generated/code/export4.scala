object LWE_Regev {

abstract sealed class int
final case class int_of_integer(a : BigInt) extends int

def integer_of_int(x0 : int) : BigInt = x0 match {
  case int_of_integer(k) => k
}

def plus_inta(k : int, l : int) : int =
  int_of_integer(integer_of_int(k) + integer_of_int(l))

trait plus[A] {
  val `LWE_Regev.plus` : (A, A) => A
}
def plus[A](a : A, b : A)(implicit A: plus[A]) : A = A.`LWE_Regev.plus`(a, b)
object plus {
  implicit def `LWE_Regev.plus_int` : plus[int] = new plus[int] {
    val `LWE_Regev.plus` = (a : int, b : int) => plus_inta(a, b)
  }
}

def zero_inta : int = int_of_integer(BigInt(0))

trait zero[A] {
  val `LWE_Regev.zero` : A
}
def zero[A](implicit A: zero[A]) : A = A.`LWE_Regev.zero`
object zero {
  implicit def `LWE_Regev.zero_int` : zero[int] = new zero[int] {
    val `LWE_Regev.zero` = zero_inta
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add {
  implicit def `LWE_Regev.semigroup_add_int` : semigroup_add[int] = new
    semigroup_add[int] {
    val `LWE_Regev.plus` = (a : int, b : int) => plus_inta(a, b)
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add {
  implicit def `LWE_Regev.monoid_add_int` : monoid_add[int] = new
    monoid_add[int] {
    val `LWE_Regev.zero` = zero_inta
    val `LWE_Regev.plus` = (a : int, b : int) => plus_inta(a, b)
  }
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a : num) extends num
final case class Bit1(a : num) extends num

abstract sealed class lwe_ciphertext_ext[A]
final case class lwe_ciphertext_exta[A](a : List[int], b : int, c : A) extends
  lwe_ciphertext_ext[A]

abstract sealed class lwe_public_key_ext[A]
final case class lwe_public_key_exta[A](a : List[List[int]], b : List[int],
 c : A)
  extends lwe_public_key_ext[A]

abstract sealed class lwe_secret_key_ext[A]
final case class lwe_secret_key_exta[A](a : List[int], b : A) extends
  lwe_secret_key_ext[A]

def id[A] : A => A = ((x : A) => x)

def comp[A, B, C](f : A => B, g : C => A) : C => B = ((x : C) => f(g(x)))

def zip[A, B](xs : List[A], ys : List[B]) : List[(A, B)] = (xs, ys) match {
  case (Nil, ys) => Nil
  case (xs, Nil) => Nil
  case (x :: xs, y :: ys) => (x, y) :: zip[A, B](xs, ys)
}

def maps[A, B](f : A => List[B], x1 : List[A]) : List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def foldr[A, B](f : A => B => B, x1 : List[A]) : B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def map[A, B](f : A => B, x1 : List[A]) : List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def transpose[A](x0 : List[List[A]]) : List[List[A]] = x0 match {
  case Nil => Nil
  case Nil :: xss => transpose[A](xss)
  case (x :: xs) :: xss =>
    (x :: maps[List[A],
                A](((a : List[A]) => (a match {
case Nil => Nil
case h :: _ => List(h)
                                      })),
                    xss)) ::
      transpose[A](xs :: maps[List[A],
                               List[A]](((a : List[A]) =>
  (a match {
     case Nil => Nil
     case _ :: t => List(t)
   })),
 xss))
}

def apsnd[A, B, C](f : A => B, x1 : (C, A)) : (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def divmod_integer(k : BigInt, l : BigInt) : (BigInt, BigInt) =
  (k == BigInt(0) match { case true => (BigInt(0), BigInt(0))
    case false => (BigInt(0) < l match {
                    case true => (BigInt(0) < k match {
                                   case true => ((k: BigInt) => (l: BigInt) =>
          l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l)
                                   case false => {
           val (r, s) =
             ((k: BigInt) => (l: BigInt) =>
               l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l) : ((BigInt,
                                  BigInt));
           (s == BigInt(0) match { case true => ((- r), BigInt(0))
             case false => ((- r) - BigInt(1), l - s) })
         }
                                   })
                    case false => (l == BigInt(0) match {
                                    case true => (BigInt(0), k)
                                    case false => apsnd[BigInt, BigInt,
                 BigInt](((a : BigInt) => (- a)),
                          (k < BigInt(0) match {
                            case true => ((k: BigInt) => (l: BigInt) =>
   l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l)
                            case false => {
    val (r, s) =
      ((k: BigInt) => (l: BigInt) =>
        l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l) : ((BigInt,
                           BigInt));
    (s == BigInt(0) match { case true => ((- r), BigInt(0))
      case false => ((- r) - BigInt(1), (- l) - s) })
  }
                            }))
                                    })
                    })
    })

def snd[A, B](x0 : (A, B)) : B = x0 match {
  case (x1, x2) => x2
}

def modulo_integer(k : BigInt, l : BigInt) : BigInt =
  snd[BigInt, BigInt](divmod_integer(k, l))

def modulo_int(k : int, l : int) : int =
  int_of_integer(modulo_integer(integer_of_int(k), integer_of_int(l)))

def fst[A, B](x0 : (A, B)) : A = x0 match {
  case (x1, x2) => x1
}

def divide_integer(k : BigInt, l : BigInt) : BigInt =
  fst[BigInt, BigInt](divmod_integer(k, l))

def divide_int(k : int, l : int) : int =
  int_of_integer(divide_integer(integer_of_int(k), integer_of_int(l)))

def minus_int(k : int, l : int) : int =
  int_of_integer(integer_of_int(k) - integer_of_int(l))

def less_int(k : int, l : int) : Boolean = integer_of_int(k) < integer_of_int(l)

def dist0(q : int, d : int) : int =
  {
    val da = modulo_int(d, q) : int;
    (less_int(divide_int(q, int_of_integer(BigInt(2))), da) match {
      case true => minus_int(q, da) case false => da })
  }

def vec_add(xs : List[int], ys : List[int]) : List[int] =
  map[(int, int),
       int](((a : (int, int)) => {
                                   val (aa, b) = a : ((int, int));
                                   plus_inta(aa, b)
                                 }),
             zip[int, int](xs, ys))

def vec_mod(v : List[int], q : int) : List[int] =
  map[int, int](((x : int) => modulo_int(x, q)), v)

def decode_bit(q : int, d : int) : Boolean =
  less_int(divide_int(q, int_of_integer(BigInt(4))), dist0(q, d))

def encode_bit(q : int, b : Boolean) : int =
  (b match { case true => divide_int(q, int_of_integer(BigInt(2)))
    case false => zero_inta })

def sum_list[A : monoid_add](xs : List[A]) : A =
  (foldr[A, A](((a : A) => (b : A) => plus[A](a, b)), xs)).apply(zero[A])

def times_int(k : int, l : int) : int =
  int_of_integer(integer_of_int(k) * integer_of_int(l))

def inner_prod(u : List[int], v : List[int]) : int =
  sum_list[int](map[(int, int),
                     int](((a : (int, int)) =>
                            {
                              val (aa, b) = a : ((int, int));
                              times_int(aa, b)
                            }),
                           zip[int, int](u, v)))

def sk_s[A](x0 : lwe_secret_key_ext[A]) : List[int] = x0 match {
  case lwe_secret_key_exta(sk_s, more) => sk_s
}

def ct_v[A](x0 : lwe_ciphertext_ext[A]) : int = x0 match {
  case lwe_ciphertext_exta(ct_u, ct_v, more) => ct_v
}

def ct_u[A](x0 : lwe_ciphertext_ext[A]) : List[int] = x0 match {
  case lwe_ciphertext_exta(ct_u, ct_v, more) => ct_u
}

def lwe_decrypt(sk : lwe_secret_key_ext[Unit], q : int,
                 ct : lwe_ciphertext_ext[Unit]) : Boolean
  =
  {
    val a =
      modulo_int(minus_int(ct_v[Unit](ct),
                            inner_prod(sk_s[Unit](sk), ct_u[Unit](ct))),
                  q) : int;
    decode_bit(q, a)
  }

def mat_vec_mult(a : List[List[int]], x : List[int]) : List[int] =
  map[List[int], int](((row : List[int]) => inner_prod(row, x)), a)

def mat_transpose_vec_mult(a : List[List[int]], r : List[int]) : List[int] =
  mat_vec_mult(transpose[int](a), r)

def pk_b[A](x0 : lwe_public_key_ext[A]) : List[int] = x0 match {
  case lwe_public_key_exta(pk_A, pk_b, more) => pk_b
}

def pk_A[A](x0 : lwe_public_key_ext[A]) : List[List[int]] = x0 match {
  case lwe_public_key_exta(pk_A, pk_b, more) => pk_A
}

def lwe_encrypt(pk : lwe_public_key_ext[Unit], q : int, r : List[int],
                 m : Boolean) : lwe_ciphertext_ext[Unit]
  =
  {
    val u = vec_mod(mat_transpose_vec_mult(pk_A[Unit](pk), r), q) : (List[int])
    val v =
      modulo_int(plus_inta(inner_prod(pk_b[Unit](pk), r), encode_bit(q, m)),
                  q) : int;
    lwe_ciphertext_exta[Unit](u, v, ())
  }

} /* object LWE_Regev */
