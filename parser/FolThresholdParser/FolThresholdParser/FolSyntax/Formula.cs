using System;
using System.Collections.Generic;
using System.Diagnostics;
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

        protected internal abstract IEnumerable<KeyValuePair<string, string>> BoundVariables { get; }

        public string ToBoundIvyAxiomActual(Dictionary<string, Identifier> identifiers)
        {
            var vars = BoundVariables;
            return ToBoundIvyAxiom(identifiers.Where(identifier => identifier.Value.Constant).Concat(
                    vars.Select(variable =>
                        new KeyValuePair<string, Identifier>(variable.Key, identifiers[variable.Value])))
                .ToDictionary(pair => pair.Key, pair => pair.Value));
        }

        public abstract string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers);
    }

    public class FormulaOperation : Formula
    {
        public Formula Form1 { get; protected set; }
        public FormulaOp Op { get; protected set; }
        public Formula Form2 { get; protected set; }

        public override IEnumerable<string> VariablesToBind => Form1.VariablesToBind.Concat(Form2.VariablesToBind);

        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables =>
            Form1.BoundVariables.Concat(Form2.BoundVariables);

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            char op;
            switch (Op)
            {
                case FormulaOp.And:
                    op = '&';
                    break;
                case FormulaOp.Or:
                    op = '|';
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }

            return $"{Form1.ToBoundIvyAxiom(identifiers)} {op} {Form2.ToBoundIvyAxiom(identifiers)}";
        }

        public FormulaOperation(Formula form1, SyntaxKind natOperation, Formula form2)
        {
            Form1 = form1;
            Op = GetOperation(natOperation);
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
    }

    public class FormulaNot : Formula
    {
        private readonly Formula _inner;

        public FormulaNot(Formula inner)
        {
            _inner = inner;
        }

        public override IEnumerable<string> VariablesToBind => _inner.VariablesToBind;
        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables => _inner.BoundVariables;

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            return $"~{_inner.ToBoundIvyAxiom(identifiers)}";
        }
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

        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables =>
            _inner.BoundVariables.Concat(new[] {new KeyValuePair<string, string>(_varName, _varType)});

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            string bind;
            switch (_bindType)
            {
                case BindType.ExistsSet:
                    bind = "exists";
                    break;
                case BindType.ForallSet:
                    bind = "forall";
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }

            return $"{bind} {_varName.ToUpper()}:quorum_{_varType.ToLower()}. {_inner.ToBoundIvyAxiom(identifiers)}";
        }

        public static Formula ParseInternal(SyntaxKind bindType, ArrayView<Token> tokens, Formula inner)
        {
            if (tokens.Length == 0) return inner;
            if (tokens[0].Type != SyntaxKind.VariableNameToken ||
                tokens[1].Type != SyntaxKind.ColonToken ||
                tokens[2].Type != SyntaxKind.VariableNameToken ||
                tokens[3].Type != SyntaxKind.CommaToken &&
                tokens[3].Type != SyntaxKind.DotToken)
                throw new Exception("Illegal formula found");
            return new FormulaBind(bindType, tokens[2].Value, tokens[0].Value,
                ParseInternal(bindType, tokens.Skip(4), inner));
        }
    }

    public class NaturalFormula : Formula
    {        
        protected NaturalExpression Expr1, Expr2;
        protected NatRelation Rel;

        public NaturalFormula(NaturalExpression expr1, SyntaxKind comparisonOp, NaturalExpression expr2)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            Rel = ToNatRelation(comparisonOp);
        }

        public static Formula Parse(ArrayView<Token> tokens)
        {
            return Parse(tokens, FormulaType.Natural);
        }

        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables => new KeyValuePair<string, string>[] { };

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
        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            throw new NotImplementedException();
        }
    }

    public class SetFormula : Formula
    {
        protected SetExpression Expr1, Expr2;
        protected SetRelation Rel;

        public SetFormula(SetExpression expr1, SyntaxKind comparisonOp, SetExpression expr2)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            Rel = ToSetRelation(comparisonOp);
        }

        public static Formula Parse(ArrayView<Token> tokens)
        {
            return Parse(tokens, FormulaType.Set);
        }

        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables => new KeyValuePair<string, string>[] { };

        public enum SetRelation
        {
            Equal,
            NotEuqal,
            Subseteq
        }

        public static SetRelation ToSetRelation(SyntaxKind comparisonOp)
        {
            switch (comparisonOp)
            {
                case SyntaxKind.LeqThanToken:
                    return SetRelation.Subseteq;
                case SyntaxKind.EqualToken:
                    return SetRelation.Equal;
                case SyntaxKind.InEqualToken:
                    return SetRelation.NotEuqal;
                default:
                    throw new Exception($"Illegal syntax kind {comparisonOp}");
            }
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);
        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            var expr1Ivy = Expr1.ToIvyAxiom(identifiers);
            var expr2Ivy = Expr2.ToIvyAxiom(identifiers);
            switch (Rel)
            {
                case SetRelation.Equal:
                    return $"forall N:node. {expr1Ivy} <-> {expr2Ivy}";
                case SetRelation.NotEuqal:
                    return $"~(forall N:node. {expr1Ivy} <-> {expr2Ivy})";
                case SetRelation.Subseteq:
                    return $"forall N:node. {expr1Ivy} -> {expr2Ivy}";
                default:
                    throw new ArgumentOutOfRangeException();
            }
        }
    }
}
