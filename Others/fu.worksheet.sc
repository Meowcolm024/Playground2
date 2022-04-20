
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

