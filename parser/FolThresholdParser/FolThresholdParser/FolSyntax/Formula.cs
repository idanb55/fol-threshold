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

        public IEnumerable<KeyValuePair<string, FormulaBind.BapaBindType>> GetVariablesToBind(Dictionary<string, Identifier> identifiers)
        {
            var res = new Dictionary<string, FormulaBind.BapaBindType>();
            foreach (var variable in VariablesToBind)
            {
                var type = Identifier.BapaBindType(identifiers, variable);
                res[variable] = type;
            }
            return res.OrderBy(pair => pair.Value);
        }

        public string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            var formula = ToIvyAxiom();
            foreach (var bind in GetVariablesToBind(identifiers))
            {
                var varName = bind.Key;
                var quorumName = varName.TrimEnd('0', '1', '2', '3', '4', '5', '6', '7', '8', '9');
                switch (bind.Value)
                {
                    case FormulaBind.BapaBindType.Forallset:
                        formula = $"forall {varName}:quorum_{quorumName}. {formula}";
                        break;
                    case FormulaBind.BapaBindType.Existsset:
                        formula = $"exsits {varName}:quorum_{quorumName}. {formula}";
                        break;
                    default:
                        throw new ArgumentOutOfRangeException();
                }
            }

            return formula;
        }

        public abstract string ToIvyAxiom();
    }

    public class FormulaBind : Formula
    {
        private readonly BapaBindType _type;
        private readonly string _varName;
        private readonly Formula _inner;

        public enum BapaBindType
        {
            Existsset,
            Forallset,
            Existsnat,
            Forallnat
        }

        public FormulaBind(BapaBindType type, string varName, Formula inner)
        {
            _type = type;
            _varName = varName;
            _inner = inner;
        }

        public override IEnumerable<string> VariablesToBind =>
            _inner.VariablesToBind.Where(variable => !string.Equals(variable, _varName));

        public override string ToIvyAxiom()
        {
            throw new NotImplementedException();
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

        internal static NaturalFormula ParseInternal(ArrayView<Token> tokens)
        {
            var operatorIndex = tokens.IndexOfFirstSyntaxKind(SyntaxGeneralType.ComparisonOperators);

            return new NaturalFormula(NaturalExpression.Parse(tokens.Take(operatorIndex)),
                tokens[operatorIndex].Type, NaturalExpression.Parse(tokens.Skip(operatorIndex + 1)));
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

        private NatRelation ToNatRelation()
        {
            return ToNatRelation(ComparisonOp);
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);

        public override string ToIvyAxiom()
        {
            throw new Exception("Naturals cannot be a part of Ivy axiom");
        }
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

        internal static SetFormula ParseInternal(ArrayView<Token> tokens)
        {
            var operatorIndex = tokens.IndexOfFirstSyntaxKind(SyntaxGeneralType.ComparisonOperators);

            return new SetFormula(SetExpression.Parse(tokens.Take(operatorIndex)),
                tokens[operatorIndex].Type, SetExpression.Parse(tokens.Skip(operatorIndex + 1)));
        }

        public enum SetRelation
        {
            Subset,
            Subseteq
        }

        private SetRelation ToSetRelation()
        {
            switch (ComparisonOp)
            {
                case SyntaxKind.LeqThanToken:
                    return SetRelation.Subseteq;
                default:
                    throw new Exception($"Illegal syntax kind {ComparisonOp}");
            }
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);

        public override string ToIvyAxiom()
        {
            return "forall N:node. " + Expr1.ToIvyAxiom() + " -> " + Expr2.ToIvyAxiom();
        }
    }
}
