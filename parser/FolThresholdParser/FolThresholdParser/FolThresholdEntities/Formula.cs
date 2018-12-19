﻿using System;
using System.Collections.Generic;
using System.Data;
using System.Linq;
using System.Text.RegularExpressions;
using FolThresholdParser.BapaFormula;
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

        public abstract IEnumerable<string> VariablesToBind { get; }

        public Dictionary<string, BapaBind.BapaBindType> GetVariablesToBind(Dictionary<string, Identifier> identifiers)
        {
            var res = new Dictionary<string, BapaBind.BapaBindType>();
            foreach (var variable in VariablesToBind)
            {
                var type = Identifier.BapaBindType(identifiers, variable);
                res[variable] = type;
            }
            return res;
        }

        public BapaFormula.BapaFormula ToBoundBapaFormula(Dictionary<string, Identifier> identifiers)
        {
            var formula = ToBapaFormula();
            foreach (var bind in GetVariablesToBind(identifiers))
            {
                formula = new BapaBind(bind.Value, bind.Key, formula);
            }

            return formula;
        }

        public abstract BapaFormula.BapaFormula ToBapaFormula();
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

        public static BapaNatRelation.NatRelation ToNatRelation(SyntaxKind comparisonOp)
        {
            switch (comparisonOp)
            {
                case SyntaxKind.EqualToken:
                    return BapaNatRelation.NatRelation.Inteq;
                case SyntaxKind.InEqualToken:
                    return BapaNatRelation.NatRelation.Intneq;

                case SyntaxKind.GreaterThanToken:
                    return BapaNatRelation.NatRelation.Greater;
                case SyntaxKind.GeqThanToken:
                    return BapaNatRelation.NatRelation.Geq;

                case SyntaxKind.LessThanToken:
                    return BapaNatRelation.NatRelation.Less;
                case SyntaxKind.LeqThanToken:
                    return BapaNatRelation.NatRelation.Leq;

                default:
                    throw new Exception($"Illegal syntax kind {comparisonOp}");
            }
        }

        private BapaNatRelation.NatRelation ToNatRelation()
        {
            return ToNatRelation(ComparisonOp);
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);

        public override BapaFormula.BapaFormula ToBapaFormula()
        {
            return new BapaNatRelation(ToNatRelation(), Expr1.ToBapaNatExpression(), Expr2.ToBapaNatExpression());
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

        public override BapaFormula.BapaFormula ToBapaFormula()
        {
            return new BapaNatRelation(BapaNatRelation.NatRelation.Intneq, new BapaCard(Expr.ToBapaSetExpression()), new BapaNatConst(0));
        }

        public override IEnumerable<string> VariablesToBind => Expr.VariablesToBind;
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

        private BapaSetRelation.SetRelation ToSetRelation()
        {
            switch (ComparisonOp)
            {
                case SyntaxKind.LessThanToken:
                    return BapaSetRelation.SetRelation.Subset;
                case SyntaxKind.LeqThanToken:
                    return BapaSetRelation.SetRelation.Subseteq;
                default:
                    throw new Exception($"Illegal syntax kind {ComparisonOp}");
            }
        }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);

        public override BapaFormula.BapaFormula ToBapaFormula()
        {
            return new BapaSetRelation(ToSetRelation(), Expr1.ToBapaSetExpression(), Expr1.ToBapaSetExpression());
        }
    }
}
