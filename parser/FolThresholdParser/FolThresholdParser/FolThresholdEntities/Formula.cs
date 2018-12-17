using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolThresholdEntities
{
    public abstract class Formula
    {
        public bool Conjecture { get; protected set; }

        protected Formula(bool conjecture)
        {
            Conjecture = conjecture;
        }

        public static Formula Parse(ArrayView<Token> tokens)
        {
            var conjecture = tokens[0].Type == SyntaxKind.ConjectureKeyword;
            switch (tokens[1].Type)
            {
                case SyntaxKind.NaturalKeyword:
                    return NaturalFormula.Parse(conjecture, tokens.Skip(2));
                case SyntaxKind.NonEmptyKeyword:
                    return NonEmptySetFormula.Parse(conjecture, tokens.Skip(2));
                case SyntaxKind.RelationKeyword:
                    return SetRelationFormula.Parse(conjecture, tokens.Skip(2));
                default:
                    return null;
            }
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

        public static NaturalFormula Parse(bool conjecture, ArrayView<Token> tokens)
        {
            var operatorIndex = tokens.IndexOfFirstSyntaxKind(SyntaxGeneralType.ComparisonOperators);

            return new NaturalFormula(conjecture, NaturalExpression.Parse(tokens.Take(operatorIndex)),
                tokens[operatorIndex].Type, NaturalExpression.Parse(tokens.Skip(operatorIndex + 1)));
        }
    }

    public class NonEmptySetFormula : Formula
    {
        protected SetExpression Expr;

        public NonEmptySetFormula(bool conjecture, SetExpression expr) : base(conjecture)
        {
            Expr = expr;
        }

        public static NonEmptySetFormula Parse(bool conjecture, ArrayView<Token> tokens)
        {
            return new NonEmptySetFormula(conjecture, SetExpression.Parse(tokens));
        }
    }

    public class SetRelationFormula : Formula
    {
        protected SetExpression Expr1, Expr2;
        protected SyntaxKind ComparisonOp;

        public SetRelationFormula(bool conjecture, SetExpression expr1, SyntaxKind comparisonOp, SetExpression expr2) : base(conjecture)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            ComparisonOp = comparisonOp;
        }

        public static SetRelationFormula Parse(bool conjecture, ArrayView<Token> tokens)
        {
            var operatorIndex = tokens.IndexOfFirstSyntaxKind(SyntaxGeneralType.ComparisonOperators);

            return new SetRelationFormula(conjecture, SetExpression.Parse(tokens.Take(operatorIndex)),
                tokens[operatorIndex].Type, SetExpression.Parse(tokens.Skip(operatorIndex + 1)));
        }
    }
}
