import java.lang.reflect.Field

trait Functor[F[_]]:
    def fmap[A, B](v: F[A], f: A => B): F[B]

trait Applicative[F[_]] extends Functor[F]:
    def pure[A](x: A): F[A]
    def ap[A, B](f: F[A => B], x: F[A]): F[B]

    def fmap[A, B](v: F[A], f: A => B): F[B] = ap(pure(f), v)

trait Monad[M[_]] extends Applicative[M]:
    def bind[A, B](x: M[A], f: A => M[B]): M[B]
    
    def ap[A, B](f: M[A => B], x: M[A]): M[B] =
        bind(x, (v => bind(f, (g => pure(g(v))))))

trait Monoid[M]:
    def mempty: M
    def mappend(lhs: M, rhs: M): M

implicit object OptionMonad extends Monad[Option]:
    def pure[A](x: A): Option[A] = Some(x)
    def bind[A, B](x: Option[A], f: A => Option[B]): Option[B] = x match
        case None    => None
        case Some(x) => f(x)
 
implicit object ListFunctor extends Functor[List]:
    def fmap[A, B](v: List[A], f: A => B): List[B] = v match
        case Nil   => Nil
        case x::xs => f(x)::fmap(xs, f)

implicit object ListMonoid extends Monoid[List[?]]:
    def mempty = Nil
    def mappend(lhs: List[?], rhs: List[?]): List[?] = lhs ++ rhs

implicit object intMonoid extends Monoid[Int]:
    def mempty = 0
    def mappend(lhs: Int, rhs: Int) = lhs + rhs

def liftAdd1[F[_]](x: F[Int])(implicit functorT: Functor[F]): F[Int] =
    functorT.fmap(x, _+1)

def dupMonoid[M](xs: M)(implicit monoidM: Monoid[M]): M =
    monoidM.mappend(xs, xs)

liftAdd1[Option](Some(2))
liftAdd1(1::2::Nil)
dupMonoid(1::2::3::Nil)(ListMonoid)
dupMonoid(6)

trait FieldA[A]:
    def _a: A

trait FieldB[B]:
    def _b: B

case class Haha(_a: Int) extends FieldA[Int]
case class Omg(_b: String) extends FieldB[String]
case class Bang(_a: Int, _b: String) extends FieldA[Int] with FieldB[String]

def useBoth[A, B](hi: FieldA[A], lo: FieldB[B]) =
    s"_a : ${hi._a} ; _b :${lo._b}"

useBoth(Haha(123), Omg("aaaaaa"))
useBoth(Bang(666, "omg"), Omg("233"))

implicit class FunAp[A, B](self: A => B):
    def $(p: A): B = self(p)

def add(x: Int)(y: Int): Int = x + y

val res = add $ 2 + 3 * 6 $ 6
