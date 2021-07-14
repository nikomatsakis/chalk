#[macro_use]
mod util;

mod assoc_const;
mod assoc_ty;
mod built_ins;
mod const_;
mod dyn_;
mod enum_;
mod fn_;
mod formatting;
mod impl_;
mod lifetimes;
mod opaque_ty;
mod self_;
mod struct_;
mod trait_;
mod unique_names;
mod where_clauses;

use self::util::*;
