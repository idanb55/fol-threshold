namespace FolThresholdParser
{
    public abstract class Formula
    {
        public bool Conjecture { get; protected set; }

        protected Formula(bool conjecture)
        {
            Conjecture = conjecture;
        }
    }

    public class NaturalFormula : Formula
    {        
        protected NaturalExpression Expr1, Expr2;
        protected SyntaxKind ComparisonOp;

        public NaturalFormula(bool conjecture, NaturalExpression expr1, SyntaxKind comparisonOp, NaturalExpression expr2) : base(conjecture)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            ComparisonOp = comparisonOp;
        }
    }

    public class NonEmptySetFormula : Formula
    {        
        protected SetExpression Expr;        

        public NonEmptySetFormula(bool conjecture, SetExpression expr) : base(conjecture)
        {
            Expr = expr;
        }
    }
}
