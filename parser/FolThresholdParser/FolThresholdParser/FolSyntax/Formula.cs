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
            if (indexOfOperation > 0)
            {
                return new FormulaOperation(Parse(tokens.Take(indexOfOperation), type),
                    tokens[indexOfOperation].Type,
                    Parse(tokens.Skip(indexOfOperation + 1), type));
            }
            
            // should be a relation now
            if (tokens[0].Type == SyntaxKind.VariableNameToken)
            {
                var relationName = tokens[0].Value;
                if(tokens[1].Type != SyntaxKind.OpenParenthesisToken)
                    throw new Exception("expected '('");
                var indexOfCloseParenthesis = tokens.Skip(1).IndexOfCloseParenthesis();
                if (indexOfCloseParenthesis < 0)
                    throw new Exception("Illegal formula");
                if (indexOfCloseParenthesis + 1 != tokens.Length - 2)
                    throw new Exception("Illegal formula");

                return new SetRelationFormula(SetExpression.Parse(tokens.Skip(2).Take(indexOfCloseParenthesis)), relationName);
            }

            throw new Exception("Illegal formula format");
        }

        protected internal abstract IEnumerable<FormulaBind.Bind> BoundVariables { get; }

        private Dictionary<string, Identifier> GetIdentifiersWithBoundVariables(Dictionary<string, Identifier> identifiers)
        {
            return identifiers.Where(identifier => identifier.Value.Constant).Concat(
                BoundVariables.Select(bind =>
                    new KeyValuePair<string, Identifier>(bind.VarName, identifiers[bind.VarType]))).ToDict();
        }

        public string ToBoundIvyAxiomActual(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            return ToBoundIvyAxiom(GetIdentifiersWithBoundVariables(identifiers), quorums);
        }

        public string GetSmtAssertActual(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            return GetSmtAssert(GetIdentifiersWithBoundVariables(identifiers), quorums);
        }

        public abstract string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers, List<Quorum> quorums);
        public abstract string GetSmtAssert(Dictionary<string, Identifier> identifiers, List<Quorum> quorums);
        public abstract Formula Negate();
        public virtual IEnumerable<FormulaBind.Bind> Release(FormulaBind.BindType bindType) { yield break; }
    }

    public class FormulaOperation : Formula
    {
        public Formula Form1 { get; protected set; }
        public FormulaOp Op { get; protected set; }
        public Formula Form2 { get; protected set; }

        public override IEnumerable<string> VariablesToBind => Form1.VariablesToBind.Concat(Form2.VariablesToBind);

        protected internal override IEnumerable<FormulaBind.Bind> BoundVariables =>
            Form1.BoundVariables.Concat(Form2.BoundVariables);

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
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

            return $"{Form1.ToBoundIvyAxiom(identifiers, quorums)} {op} {Form2.ToBoundIvyAxiom(identifiers, quorums)}";
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            return $"({Op.ToString().ToLower()} {Form1.GetSmtAssert(identifiers, quorums)} {Form2.GetSmtAssert(identifiers, quorums)})";
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
        protected internal override IEnumerable<FormulaBind.Bind> BoundVariables => _inner.BoundVariables;

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            return $"~{_inner.ToBoundIvyAxiom(identifiers, quorums)}";
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            return $"(not {_inner.GetSmtAssert(identifiers, quorums)})";
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
        private readonly Bind _bind;
        private readonly Formula _inner;
        private bool _released;

        public enum BindType
        {
            ExistsSet = SyntaxKind.ExistsSetKeyword,
            ForallSet = SyntaxKind.ForallSetKeyword,
        }

        public FormulaBind(BindType type, string varType, string varName, Formula inner)
        {
            _bind = new Bind(type, varType, varName);
            _inner = inner;
        }

        public FormulaBind(SyntaxKind type, string varType, string varName, Formula inner) : this((BindType)type, varType, varName, inner)
        {
        }

        public override IEnumerable<string> VariablesToBind =>
            _inner.VariablesToBind.Where(variable => !string.Equals(variable, _bind.VarName));

        protected internal override IEnumerable<Bind> BoundVariables => _inner.BoundVariables.Concat(new[] {_bind});

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            if (_released) return _inner.ToBoundIvyAxiom(identifiers, quorums);
            return $"{GetBindTypeTextual()} {_bind.VarName.ToUpper()}:quorum_{_bind.VarType.ToLower()}. {_inner.ToBoundIvyAxiom(identifiers, quorums)}";
        }

        private string GetBindTypeTextual()
        {
            string bind;
            switch (_bind.BindType)
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

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            if (_released) return _inner.GetSmtAssert(identifiers, quorums);
            return $"({GetBindTypeTextual()} (({_bind.VarName.ToUpper()} (Set Int))) {_inner.GetSmtAssert(identifiers, quorums)})"; // TODO add the quorum rule as an assumption
        }

        public override Formula Negate()
        {
            return new FormulaBind(_bind.BindType == BindType.ForallSet ? BindType.ExistsSet : BindType.ForallSet, _bind.VarType, _bind.VarName, _inner.Negate());
        }

        public override string ToString()
        {
            if (_released) return _inner.ToString();
            return $"{GetBindTypeTextual()} {_bind.VarName}:{_bind.VarType}. {_inner}";
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

        public override IEnumerable<Bind> Release(BindType bindType)
        {
            if (bindType != _bind.BindType) yield break;
            _released = true;
            yield return _bind;
            foreach (var bind in _inner.Release(bindType))
            {
                yield return bind;
            }
        }

        public struct Bind
        {
            public readonly BindType BindType;
            public readonly string VarType;
            public readonly string VarName;

            public Bind(BindType type, string varType, string varName)
            {
                BindType = type;
                VarType = varType;
                VarName = varName;
            }
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

        protected internal override IEnumerable<FormulaBind.Bind> BoundVariables => new FormulaBind.Bind[] { };

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
        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            throw new NotImplementedException();
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            var reduce1 = NatConstDivExpression.Reduce(Expr1);
            var reduce2 = NatConstDivExpression.Reduce(Expr2);
            var gcd = NatConstDivExpression.Gcd(reduce1.Item2, reduce2.Item2);

            var expr1 = NatConstMulExpression.Mul(reduce2.Item2 / gcd, reduce1.Item1);
            var expr2 = NatConstMulExpression.Mul(reduce1.Item2 / gcd, reduce2.Item1);

            return $"({Tokenizer.Keywords[(SyntaxKind) Rel]} {expr1.GetSmtAssert(identifiers)} {expr2.GetSmtAssert(identifiers)})";
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

    public class SetRelationFormula : Formula
    {
        protected SetExpression Expr;
        protected string RelationName;

        public SetRelationFormula(SetExpression expr, string relationName)
        {
            Expr = expr;
            RelationName = relationName;
        }

        public override IEnumerable<string> VariablesToBind => Expr.VariablesToBind;
        protected internal override IEnumerable<FormulaBind.Bind> BoundVariables => new FormulaBind.Bind[] { };

        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            var quorum = quorums.SingleOrDefault(quorumRel => string.Equals(quorumRel.Name, RelationName));
            if (quorum == null) throw new Exception("Unknown quorum relation");

            var formula = new FormulaBind(FormulaBind.BindType.ExistsSet, quorum.Name.ToLower(), quorum.Name.ToUpper(),
                new SetFormula(Expr, SetFormula.SetRelation.Equal, new SetVarExpression(quorum.Name.ToLower())));
            return formula.ToBoundIvyAxiom(
                identifiers.Add(new KeyValuePair<string, Identifier>(quorum.Name.ToLower(), quorum)).ToDict(), quorums);
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            var quorum = quorums.SingleOrDefault(quorumRel => string.Equals(quorumRel.Name, RelationName));
            if (quorum == null) throw new Exception("Unknown quorum relation");

            var formula = new NaturalFormula(new NatCardExpression(Expr), quorum.Operation, quorum.Expression);
            return formula.GetSmtAssert(identifiers, quorums);
        }

        public override string ToString()
        {
            return $"{RelationName}({Expr})";
        }

        public override Formula Negate()
        {
            return new FormulaNot(this);
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

        protected internal override IEnumerable<FormulaBind.Bind> BoundVariables => new FormulaBind.Bind[] { };

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
        public override string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
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

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers, List<Quorum> quorums)
        {
            var expr1Smt = Expr1.GetSmtAssert(identifiers);
            var expr2Smt = Expr2.GetSmtAssert(identifiers);
            switch (Rel)
            {
                case SetRelation.Equal:
                    return $"(= {expr1Smt} {expr2Smt})";
                case SetRelation.NotEuqal:
                    return $"(!= {expr1Smt} {expr2Smt})";
                case SetRelation.Subseteq:
                    return $"(subset {expr1Smt} {expr2Smt})";
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
