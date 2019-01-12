using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices.WindowsRuntime;
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

        private Dictionary<string, Identifier> GetIdentifiersWithBoundVariables(Dictionary<string, Identifier> identifiers)
        {
            return identifiers.Where(identifier => identifier.Value.Constant).Concat(
                BoundVariables.Select(variable =>
                    new KeyValuePair<string, Identifier>(variable.Key, identifiers[variable.Value]))).ToDictionary(pair => pair.Key, pair => pair.Value);
        }

        public string ToBoundIvyAxiomActual(Dictionary<string, Identifier> identifiers)
        {
            return ToBoundIvyAxiom(GetIdentifiersWithBoundVariables(identifiers));
        }

        public string GetSmtAssertActual(Dictionary<string, Identifier> identifiers)
        {
            return GetSmtAssert(GetIdentifiersWithBoundVariables(identifiers));
        }

        public abstract string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers);
        public abstract string GetSmtAssert(Dictionary<string, Identifier> identifiers);
        public abstract Formula Negate();
        public virtual Formula Release(FormulaBind.BindType bindType) { return this; }
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

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return $"{Op.ToString().ToLower()} ({Form1.GetSmtAssert(identifiers)}) ({Form2.GetSmtAssert(identifiers)})";
        }

        public override Formula Negate()
        {
            return new FormulaOperation(Form1.Negate(), Op == FormulaOp.And ? FormulaOp.Or : FormulaOp.And, Form2.Negate());
        }

        private FormulaOperation(Formula form1, FormulaOp natOperation, Formula form2)
        {
            Form1 = form1;
            Op = natOperation;
            Form2 = form2;
        }

        public FormulaOperation(Formula form1, SyntaxKind natOperation, Formula form2) : this(form1, (FormulaOp)natOperation, form2)
        {
        }

        public enum FormulaOp
        {
            And = SyntaxKind.AndKeyword, Or = SyntaxKind.OrKeyword
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

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return $"not ({_inner.GetSmtAssert(identifiers)})";
        }

        public override Formula Negate()
        {
            return _inner.Negate();
        }

        public override string ToString()
        {
            return $"~{_inner}";
        }
    }

    public class FormulaBind : Formula
    {
        private readonly BindType _bindType;
        private readonly string _varType;
        private readonly string _varName;
        private readonly Formula _inner;
        private bool _released;

        public enum BindType
        {
            ExistsSet = SyntaxKind.ExistsSetKeyword,
            ForallSet = SyntaxKind.ForallSetKeyword,
        }

        private FormulaBind(BindType type, string varType, string varName, Formula inner)
        {
            _bindType = type;
            _varType = varType;
            _varName = varName;
            _inner = inner;
        }

        public FormulaBind(SyntaxKind type, string varType, string varName, Formula inner) : this((BindType)type, varType, varName, inner)
        {
        }

        public override IEnumerable<string> VariablesToBind =>
            _inner.VariablesToBind.Where(variable => !string.Equals(variable, _varName));

        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables =>
            _inner.BoundVariables.Concat(new[] {new KeyValuePair<string, string>(_varName, _varType)});

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            if (_released) return _inner.ToBoundIvyAxiom(identifiers);
            return $"{GetBindTypeTextual()} {_varName.ToUpper()}:quorum_{_varType.ToLower()}. {_inner.ToBoundIvyAxiom(identifiers)}";
        }

        private string GetBindTypeTextual()
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

            return bind;
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            if (_released) return _inner.GetSmtAssert(identifiers);
            return $"{GetBindTypeTextual()} (({_varName} (Set Int))) ({_inner.GetSmtAssert(identifiers)})"; // TODO add the quorum rule as an assumption
        }

        public override Formula Negate()
        {
            return new FormulaBind(_bindType == BindType.ForallSet ? BindType.ExistsSet : BindType.ForallSet, _varType, _varName, _inner.Negate());
        }

        public override string ToString()
        {
            if (_released) return _inner.ToString();
            return $"{GetBindTypeTextual()} {_varName}:{_varType}. {_inner}";
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

        public override Formula Release(BindType bindType)
        {
            if (bindType != _bindType) return this;
            _released = true;
            _inner.Release(bindType);
            return this;
        }
    }

    public class NaturalFormula : Formula
    {        
        protected NaturalExpression Expr1, Expr2;
        protected NatRelation Rel;

        public NaturalFormula(NaturalExpression expr1, NatRelation comparisonOp, NaturalExpression expr2)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            Rel = comparisonOp;
        }

        public NaturalFormula(NaturalExpression expr1, SyntaxKind comparisonOp, NaturalExpression expr2) : this(expr1, (NatRelation)comparisonOp, expr2)
        {
        }

        public static Formula Parse(ArrayView<Token> tokens)
        {
            return Parse(tokens, FormulaType.Natural);
        }

        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables => new KeyValuePair<string, string>[] { };

        public enum NatRelation
        {
            Less = SyntaxKind.LessThanToken,
            Leq = SyntaxKind.LeqThanToken,
            Greater = SyntaxKind.GreaterThanToken,
            Geq = SyntaxKind.GeqThanToken,
            Inteq = SyntaxKind.EqualToken,
            Intneq = SyntaxKind.InEqualToken
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);
        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            throw new NotImplementedException();
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return $"{Tokenizer.Keywords[(SyntaxKind) Rel]} ({Expr1.GetSmtAssert(identifiers)}) ({Expr2.GetSmtAssert(identifiers)})";
        }

        private NatRelation GetNegOp()
        {
            switch (Rel)
            {
                case NatRelation.Less:
                    return NatRelation.Greater;
                case NatRelation.Leq:
                    return NatRelation.Geq;
                case NatRelation.Greater:
                    return NatRelation.Less;
                case NatRelation.Geq:
                    return NatRelation.Leq;
                case NatRelation.Inteq:
                    return NatRelation.Intneq;
                case NatRelation.Intneq:
                    return NatRelation.Inteq;
                default:
                    throw new ArgumentOutOfRangeException();
            }
        }

        public override Formula Negate()
        {
            return new NaturalFormula(Expr1, GetNegOp(), Expr2);
        }

        public override string ToString()
        {
            return $"{Expr1} {Tokenizer.Keywords[(SyntaxKind)Rel]} {Expr2}";
        }
    }

    public class SetFormula : Formula
    {
        protected SetExpression Expr1, Expr2;
        protected SetRelation Rel;

        public SetFormula(SetExpression expr1, SetRelation comparisonOp, SetExpression expr2)
        {
            Expr1 = expr1;
            Expr2 = expr2;
            Rel = comparisonOp;
        }

        public SetFormula(SetExpression expr1, SyntaxKind comparisonOp, SetExpression expr2) : this(expr1, (SetRelation)comparisonOp, expr2)
        {
        }

        public static Formula Parse(ArrayView<Token> tokens)
        {
            return Parse(tokens, FormulaType.Set);
        }

        protected internal override IEnumerable<KeyValuePair<string, string>> BoundVariables => new KeyValuePair<string, string>[] { };

        public enum SetRelation
        {
            Equal = SyntaxKind.EqualToken,
            NotEuqal = SyntaxKind.InEqualToken,
            Subseteq = SyntaxKind.LeqThanToken
        }

        public override Formula Negate()
        {
            if(Rel == SetRelation.Subseteq) return new SetFormula(Expr2, SetRelation.Subseteq, Expr1); // TODO: not accurate
            return new SetFormula(Expr1, Rel == SetRelation.Equal ? SetRelation.NotEuqal : SetRelation.Equal, Expr2);
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

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            var expr1Smt = Expr1.GetSmtAssert(identifiers);
            var expr2Smt = Expr2.GetSmtAssert(identifiers);
            switch (Rel)
            {
                case SetRelation.Equal:
                    return $"= ({expr1Smt}) ({expr2Smt})";
                case SetRelation.NotEuqal:
                    return $"!= ({expr1Smt}) ({expr2Smt})";
                case SetRelation.Subseteq:
                    return $"subset ({expr1Smt}) ({expr2Smt})";
                default:
                    throw new ArgumentOutOfRangeException();
            }
        }

        public override string ToString()
        {
            return $"{Expr1} {Tokenizer.Keywords[(SyntaxKind)Rel]} {Expr2}";
        }
    }
}
