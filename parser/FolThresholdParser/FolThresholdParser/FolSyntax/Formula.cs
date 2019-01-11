using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolSyntax
{
    public abstract class Formula
    {
        public abstract IEnumerable<string> VariablesToBind { get; }

        public enum FormulaType
        {
            Natural, Set
        }

        public static Formula Parse(ArrayView<Token> tokens, FormulaType type)
        {
            if (tokens[0].Type == SyntaxKind.NotKeyword)
            {
                return new FormulaNot(Parse(tokens.Skip(1), type));
            }

            if (tokens[0].Type == SyntaxKind.OpenParenthesisToken)
            {
                var indexOfCloseParenthesis = tokens.IndexOfCloseParenthesis();
                if(indexOfCloseParenthesis < 0)
                    throw new Exception("Illegal formula");
                if (indexOfCloseParenthesis + 1 != tokens.Length - 1)
                    throw new Exception("Illegal formula");

                return Parse(tokens.Skip(1).Take(indexOfCloseParenthesis), type);
            }

            if (tokens[0].Type == SyntaxKind.ForallSetKeyword || tokens[0].Type == SyntaxKind.ExistsSetKeyword)
            {
                var indexOfCloseParenthesis = tokens.IndexOfFirstSyntaxKind(SyntaxKind.DotToken);
                return FormulaBind.ParseInternal(tokens[0].Type, tokens.Skip(1).Take(indexOfCloseParenthesis), Parse(tokens.Skip(indexOfCloseParenthesis + 1), type));
            }

            var indexOfOperation = tokens.IndexOfFirstSyntaxKindNoThrow(SyntaxGeneralType.ComparisonOperators);
            if (indexOfOperation > 0)
            {
                switch (type)
                {
                    case FormulaType.Natural:
                        return new NaturalFormula(NaturalExpression.Parse(tokens.Take(indexOfOperation)),
                            tokens[indexOfOperation].Type,
                            NaturalExpression.Parse(tokens.Skip(indexOfOperation + 1)));
                    case FormulaType.Set:
                        return new SetFormula(SetExpression.Parse(tokens.Take(indexOfOperation)),
                            tokens[indexOfOperation].Type,
                            SetExpression.Parse(tokens.Skip(indexOfOperation + 1)));
                    default:
                        throw new ArgumentOutOfRangeException(nameof(type), type, null);
                }
            }

            indexOfOperation = tokens.IndexOfFirstSyntaxKindNoThrow(SyntaxGeneralType.Keyword);
            return new FormulaOperation(Parse(tokens.Take(indexOfOperation), type),
                tokens[indexOfOperation].Type,
                Parse(tokens.Skip(indexOfOperation + 1), type));
        }
    }

    public class FormulaOperation : Formula
    {
        public Formula Form1 { get; protected set; }
        public SyntaxKind Op { get; protected set; }
        public Formula Form2 { get; protected set; }

        public override IEnumerable<string> VariablesToBind => Form1.VariablesToBind.Concat(Form2.VariablesToBind);

        public FormulaOperation(Formula form1, SyntaxKind natOperation, Formula form2)
        {
            Form1 = form1;
            Op = natOperation;
            Form2 = form2;
        }

        public enum FormulaOp
        {
            And, Or
        }

        private static FormulaOp GetOperation(SyntaxKind op)
        {
            switch (op)
            {
                case SyntaxKind.AndKeyword:
                    return FormulaOp.And;
                case SyntaxKind.OrKeyword:
                    return FormulaOp.Or;
                default:
                    throw new Exception("Illegal Natural operation");
            }
        }

        public override string ToString()
        {
            return $"{Form1} {Tokenizer.Keywords[Op]} {Form2}";
        }
    }

    public class FormulaNot : Formula
    {
        private readonly Formula _inner;

        public FormulaNot(Formula inner)
        {
            _inner = inner;
        }

        public override IEnumerable<string> VariablesToBind => _inner.VariablesToBind;
    }

    public class FormulaBind : Formula
    {
        private readonly BindType _bindType;
        private readonly string _varType;
        private readonly string _varName;
        private readonly Formula _inner;

        public enum BindType
        {
            ExistsSet,
            ForallSet,
        }

        public static BindType ToBindType(SyntaxKind comparisonOp)
        {
            switch (comparisonOp)
            {
                case SyntaxKind.ExistsSetKeyword:
                    return BindType.ExistsSet;
                case SyntaxKind.ForallSetKeyword:
                    return BindType.ForallSet;
                default:
                    throw new Exception($"Illegal syntax kind {comparisonOp}");
            }
        }

        public FormulaBind(SyntaxKind type, string varType, string varName, Formula inner)
        {
            _bindType = ToBindType(type);
            _varType = varType;
            _varName = varName;
            _inner = inner;
        }

        public override IEnumerable<string> VariablesToBind =>
            _inner.VariablesToBind.Where(variable => !string.Equals(variable, _varName));

        public static Formula ParseInternal(SyntaxKind bindType, ArrayView<Token> tokens, Formula inner)
        {
            if (tokens.Length == 4) return inner;
            if (tokens[0].Type != SyntaxKind.VariableNameToken ||
                tokens[1].Type != SyntaxKind.ColonToken ||
                tokens[2].Type != SyntaxKind.VariableNameToken ||
                tokens[3].Type != SyntaxKind.CommaToken &&
                tokens[3].Type != SyntaxKind.DotToken)
                throw new Exception("Illegal formula found");
            return new FormulaBind(bindType, tokens[0].Value, tokens[2].Value,
                ParseInternal(bindType, tokens.Skip(4), inner));
        }
    }

    public class NaturalFormula : Formula
    {        
        protected NaturalExpression Expr1, Expr2;
        protected SyntaxKind ComparisonOp;

        public NaturalFormula(NaturalExpression expr1, SyntaxKind comparisonOp, NaturalExpression expr2)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            ComparisonOp = comparisonOp;
        }

        public static Formula Parse(ArrayView<Token> tokens)
        {
            return Parse(tokens, FormulaType.Natural);
        }

        public enum NatRelation
        {
            Less,
            Leq,
            Greater,
            Geq,
            Inteq,
            Intneq
        }

        public static NatRelation ToNatRelation(SyntaxKind comparisonOp)
        {
            switch (comparisonOp)
            {
                case SyntaxKind.EqualToken:
                    return NatRelation.Inteq;
                case SyntaxKind.InEqualToken:
                    return NatRelation.Intneq;

                case SyntaxKind.GreaterThanToken:
                    return NatRelation.Greater;
                case SyntaxKind.GeqThanToken:
                    return NatRelation.Geq;

                case SyntaxKind.LessThanToken:
                    return NatRelation.Less;
                case SyntaxKind.LeqThanToken:
                    return NatRelation.Leq;

                default:
                    throw new Exception($"Illegal syntax kind {comparisonOp}");
            }
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);
    }

    public class SetFormula : Formula
    {
        protected SetExpression Expr1, Expr2;
        protected SyntaxKind ComparisonOp;

        public SetFormula(SetExpression expr1, SyntaxKind comparisonOp, SetExpression expr2)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            ComparisonOp = comparisonOp;
        }

        public static Formula Parse(ArrayView<Token> tokens)
        {
            return Parse(tokens, FormulaType.Set);
        }

        public enum SetRelation
        {
            Subset,
            Subseteq
        }

        public static SetRelation ToSetRelation(SyntaxKind comparisonOp)
        {
            switch (comparisonOp)
            {
                case SyntaxKind.LeqThanToken:
                    return SetRelation.Subseteq;
                case SyntaxKind.LessThanToken:
                    return SetRelation.Subset;
                default:
                    throw new Exception($"Illegal syntax kind {comparisonOp}");
            }
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);
    }
}
