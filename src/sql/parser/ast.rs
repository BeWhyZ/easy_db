use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

use crate::sql::types::DataType;

#[derive(Debug)]

pub enum Statement {
    Begin {
        read_only: bool,
        as_of: Option<u64>,
    },
    /// COMMIT: commits a transaction.
    Commit,
    /// ROLLBACK: rolls back a transaction.
    Rollback,
    /// EXPLAIN: explains a SQL statement's execution plan.
    Explain(Box<Statement>),
    /// CREATE TABLE: creates a new table.
    CreateTable {
        /// The table name.
        name: String,
        /// Column specifications.
        columns: Vec<Column>,
    },
    /// DROP TABLE: drops a table.
    DropTable {
        /// The table to drop.
        name: String,
        /// IF EXISTS: if true, don't error if the table doesn't exist.
        if_exists: bool,
    },
    /// DELETE: deletes rows from a table.
    Delete {
        /// The table to delete from.
        table: String,
        /// WHERE: optional condition to match rows to delete.
        r#where: Option<Expression>,
    },
    /// INSERT INTO: inserts new rows into a table.
    Insert {
        /// Table to insert into.
        table: String,
        /// Columns to insert values into. If None, all columns are used.
        columns: Option<Vec<String>>,
        /// Row values to insert.
        values: Vec<Vec<Expression>>,
    },
    /// UPDATE: updates rows in a table.
    Update {
        table: String,
        set: BTreeMap<String, Option<Expression>>, // column → value, None for default value
        r#where: Option<Expression>,
    },
    /// SELECT: selects rows, possibly from a table.
    Select {
        /// Expressions to select, with an optional column alias.
        select: Vec<(Expression, Option<String>)>,
        /// FROM: tables to select from.
        from: Vec<From>,
        /// WHERE: optional condition to filter rows.
        r#where: Option<Expression>,
        /// GROUP BY: expressions to group and aggregate by.
        group_by: Vec<Expression>,
        /// HAVING: expression to filter groups by.
        having: Option<Expression>,
        /// ORDER BY: expresisions to sort by, with direction.
        order_by: Vec<(Expression, Direction)>,
        /// OFFSET: row offset to start from.
        offset: Option<Expression>,
        /// LIMIT: maximum number of rows to return.
        limit: Option<Expression>,
    },
}

/// A CREATE TABLE column definition.
#[derive(Debug)]
pub struct Column {
    pub name: String,
    pub data_type: DataType,
    pub primary_key: bool,
    pub nullable: Option<bool>,
    pub default: Option<Expression>,
    pub unique: bool,
    pub index: bool,
    pub references: Option<String>,
}

/// SQL expressions, e.g. `a + 7 > b`. Can be nested.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Expression {
    /// All columns, i.e. *.
    All,
    /// A column reference, optionally qualified with a table name.
    Column(Option<String>, String),
    /// A literal value.
    Literal(Literal),
    /// A function call (name and parameters).
    Function(String, Vec<Expression>),
    /// An operator.
    Operator(Operator),
}

#[derive(Clone, Debug)]
pub enum Literal {
    Null,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Null, Self::Null) => true,
            (Self::Boolean(a), Self::Boolean(b)) => a == b,
            (Self::Integer(a), Self::Integer(b)) => a == b,
            (Self::Float(a), Self::Float(b)) => a == b,
            (Self::String(a), Self::String(b)) => a == b,
            (_, _) => false,
        }
    }
}

impl Eq for Literal {}

impl Hash for Literal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Self::Null => {}
            Self::Boolean(b) => b.hash(state),
            Self::Integer(i) => i.hash(state),
            Self::Float(f) => f.to_bits().hash(state),
            Self::String(s) => s.hash(state),
        }
    }
}

/// ORDER BY direction.
#[derive(Debug, Default)]
pub enum Direction {
    #[default]
    Ascending,
    Descending,
}

#[derive(Debug)]
pub enum From {
    Table { name: String, alias: Option<String> },
    Join { left: Box<From>, right: Box<From>, r#type: JoinType, predicate: Option<Expression> },
}

/// Expression operators.
///
/// Since this is a recursive data structure, we have to box each child
/// expression, which incurs a heap allocation. There are clever ways to get
/// around this, but we keep it simple.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Operator {
    And(Box<Expression>, Box<Expression>), // a AND b
    Not(Box<Expression>),                  // NOT a
    Or(Box<Expression>, Box<Expression>),  // a OR b

    Equal(Box<Expression>, Box<Expression>),       // a = b
    GreaterThan(Box<Expression>, Box<Expression>), // a > b
    GreaterThanOrEqual(Box<Expression>, Box<Expression>), // a >= b
    Is(Box<Expression>, Literal),                  // IS NULL or IS NAN
    LessThan(Box<Expression>, Box<Expression>),    // a < b
    LessThanOrEqual(Box<Expression>, Box<Expression>), // a <= b
    NotEqual(Box<Expression>, Box<Expression>),    // a != b

    Add(Box<Expression>, Box<Expression>),          // a + b
    Divide(Box<Expression>, Box<Expression>),       // a / b
    Exponentiate(Box<Expression>, Box<Expression>), // a ^ b
    Factorial(Box<Expression>),                     // a!
    Identity(Box<Expression>),                      // +a
    Multiply(Box<Expression>, Box<Expression>),     // a * b
    Negate(Box<Expression>),                        // -a
    Remainder(Box<Expression>, Box<Expression>),    // a % b
    Subtract(Box<Expression>, Box<Expression>),     // a - b

    Like(Box<Expression>, Box<Expression>), // a LIKE b
}

/// JOIN types.
#[derive(Debug, PartialEq)]
pub enum JoinType {
    Cross,
    Inner,
    Left,
    Right,
}

impl core::convert::From<Literal> for Expression {
    fn from(literal: Literal) -> Self {
        Self::Literal(literal)
    }
}

impl core::convert::From<Operator> for Expression {
    fn from(op: Operator) -> Self {
        Self::Operator(op)
    }
}

impl core::convert::From<Operator> for Box<Expression> {
    fn from(op: Operator) -> Self {
        Box::new(op.into())
    }
}
