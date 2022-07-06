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

trait MonoidK[M[_]]:
    def mempty[A]: M[A]
    def mappend[A](lhs: M[A], rhs: M[A]): M[A]

implicit object OptionMonad extends Monad[Option]:
    def pure[A](x: A): Option[A] = Some(x)
    def bind[A, B](x: Option[A], f: A => Option[B]): Option[B] = x match
        case None    => None
        case Some(x) => f(x)
 
implicit object ListFunctor extends Functor[List]:
    def fmap[A, B](v: List[A], f: A => B): List[B] = v match
        case Nil   => Nil
        case x::xs => f(x)::fmap(xs, f)

implicit object ListMonoid extends MonoidK[List]:
    def mempty[A] = Nil
    def mappend[A](lhs: List[A], rhs: List[A]): List[A] = lhs ++ rhs

implicit object intMonoid extends Monoid[Int]:
    def mempty = 0
    def mappend(lhs: Int, rhs: Int) = lhs + rhs

def liftAdd1[F[_]](x: F[Int])(implicit functorT: Functor[F]): F[Int] =
    functorT.fmap(x, _+1)

def dupMonoid[M](xs: M)(implicit monoidM: Monoid[M]): M =
    monoidM.mappend(xs, xs)

def dupMonoidK[M[_], A](xs: M[A])(implicit monoidM: MonoidK[M]): M[A] =
    monoidM.mappend(xs, xs)

liftAdd1[Option](Some(2))
liftAdd1(1::2::Nil)(ListFunctor)
dupMonoidK(1::2::3::Nil)
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

class SetCounter:
    var x: Int = 1
    def get: Int = x
    def set(i: Int): Unit = x = i
    def inc: Unit = 
        val i = get
        set(i + 1)

class InstrCounter extends SetCounter:
    var y: Int = 0
    override def set(i: Int): Unit =
        y += 1
        x = i
    def access: Int = y

val ic = InstrCounter()
ic.set(5)
ic.inc
ic.get
ic.access

trait Alternative[F[_]] extends Applicative[F]:
    def or[A](a: F[A], b: F[A]): F[A]
    def empty[A]: F[A]

implicit object ListAlternative extends Alternative[List]:
    def or[A](a: List[A], b: List[A]): List[A] = a ++ b
    def empty[A]: List[A] = Nil

    def pure[A](x: A): List[A] = List(x)
    def ap[A, B](f: List[A => B], x: List[A]): List[B] = f.flatMap(x.map)
    override def fmap[A, B](v: List[A], f: A => B): List[B] = ListFunctor.fmap(v, f)

def guard[F[_]](p: Boolean)(implicit A: Alternative[F]): F[Unit] =
    if p then A.pure(()) else A.empty

val ha =
    for
        i <- 1 to 10
        _ <- guard(i % 2 == 0)
    yield
        i

