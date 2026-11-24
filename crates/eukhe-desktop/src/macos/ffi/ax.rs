//! AX element calls (port of the AX plumbing of omp
//! `crates/natives/src/desktop/macos/ax.rs`).

use std::ffi::c_void;
use std::ptr::{self, NonNull};

use objc2_application_services::{
    AXCopyMultipleAttributeOptions, AXError, AXIsProcessTrusted, AXUIElement, AXValue, AXValueType,
};
use objc2_core_foundation::{
    CFArray, CFBoolean, CFIndex, CFNull, CFNumber, CFRange, CFRetained, CFString, CFType, CGPoint,
    CGSize, Type, CFURL,
};

/// A retained `AXUIElement`; equal by `CFEqual`, hashed by `CFHash`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AxHandle(CFRetained<AXUIElement>);

/// An AX call's failure code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AxCode {
    Failure,
    IllegalArgument,
    /// The element is gone.
    InvalidElement,
    /// The app did not answer in time.
    CannotComplete,
    AttributeUnsupported,
    ActionUnsupported,
    NotImplemented,
    /// Accessibility is not granted to this process.
    ApiDisabled,
    NoValue,
    Other(i32),
}

impl AxCode {
    fn check(error: AXError) -> Result<(), Self> {
        match error {
            AXError::Success => Ok(()),
            AXError::Failure => Err(Self::Failure),
            AXError::IllegalArgument => Err(Self::IllegalArgument),
            AXError::InvalidUIElement => Err(Self::InvalidElement),
            AXError::CannotComplete => Err(Self::CannotComplete),
            AXError::AttributeUnsupported => Err(Self::AttributeUnsupported),
            AXError::ActionUnsupported => Err(Self::ActionUnsupported),
            AXError::NotImplemented => Err(Self::NotImplemented),
            AXError::APIDisabled => Err(Self::ApiDisabled),
            AXError::NoValue => Err(Self::NoValue),
            AXError(code) => Err(Self::Other(code)),
        }
    }
}

/// An attribute value, decoded at the boundary.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Value {
    Text(String),
    Bool(bool),
    Int(i64),
    /// A float number and whether it was stored in 32 bits.
    Float(f64, Width),
    Element(AxHandle),
    Elements(Vec<AxHandle>),
    Point {
        x: f64,
        y: f64,
    },
    Size {
        width: f64,
        height: f64,
    },
    Range {
        location: i64,
        length: i64,
    },
    Url(String),
    /// A value of a type no caller reads.
    Other,
}

/// The storage width of a float number, which decides how it prints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Width {
    Single,
    Double,
}

/// One attribute read: its value, `None` when it has none.
pub(crate) type Read = Result<Option<Value>, AxCode>;

/// Attribute names sent in one batched read, built once per backend.
pub(crate) struct Names(CFRetained<CFArray<CFString>>);

impl Names {
    pub(crate) fn new(names: &[&'static str]) -> Self {
        let names: Vec<CFRetained<CFString>> = names
            .iter()
            .map(|name| CFString::from_static_str(name))
            .collect();
        Self(CFArray::from_retained_objects(&names))
    }
}

/// Whether this process may use accessibility (no prompt).
pub(crate) fn trusted() -> bool {
    // SAFETY: a non-prompting TCC query without arguments.
    unsafe { AXIsProcessTrusted() }
}

/// `_AXUIElementGetWindow`: the window server id of a window element.
pub(crate) type WindowIdFn = unsafe extern "C" fn(*const AXUIElement, *mut u32) -> i32;

impl AxHandle {
    /// The application element of process `pid`.
    pub(crate) fn application(pid: i32) -> Self {
        // SAFETY: creating an application element has no preconditions; a
        // dead pid yields an element whose reads fail.
        Self(unsafe { AXUIElement::new_application(pid) })
    }

    /// The process owning the element.
    pub(crate) fn pid(&self) -> Result<i32, AxCode> {
        let mut pid = 0;
        // SAFETY: `pid` is writable for the synchronous call.
        AxCode::check(unsafe { self.0.pid(NonNull::from(&mut pid)) })?;
        Ok(pid)
    }

    /// Bounds every later request to this element's app to `seconds`.
    pub(crate) fn set_timeout(&self, seconds: f32) {
        // SAFETY: the retained element outlives the call. A refused timeout
        // keeps the system default, which only waits longer.
        let _ = unsafe { self.0.set_messaging_timeout(seconds) };
    }

    pub(crate) fn read(&self, attribute: &'static str) -> Read {
        let name = CFString::from_static_str(attribute);
        let mut out: *const CFType = ptr::null();
        // SAFETY: `out` is writable; a successful copy stores a +1 value.
        let error = unsafe { self.0.copy_attribute_value(&name, NonNull::from(&mut out)) };
        match AxCode::check(error) {
            Ok(()) => Ok(retained(out).as_deref().and_then(decode)),
            Err(AxCode::NoValue) => Ok(None),
            Err(code) => Err(code),
        }
    }

    /// `names`' values in one round trip; one entry per name, in order. A
    /// batch that fails as a whole gives each name its error.
    pub(crate) fn read_many(&self, names: &Names) -> Vec<Read> {
        let count = names.0.len();
        let mut out: *const CFArray = ptr::null();
        // SAFETY: the request is a CFArray of CFString names; `out` is
        // writable and receives a +1 CFArray on success.
        let error = unsafe {
            self.0.copy_multiple_attribute_values(
                names.0.as_opaque(),
                AXCopyMultipleAttributeOptions::empty(),
                NonNull::from(&mut out),
            )
        };
        if let Err(code) = AxCode::check(error) {
            return vec![Err(code); count];
        }
        let Some(array) = retained(out) else {
            return vec![Err(AxCode::Failure); count];
        };
        // SAFETY: every entry of the reply is a CF object.
        let values = unsafe { CFRetained::cast_unchecked::<CFArray<CFType>>(array) };
        (0..count)
            .map(|index| match values.get(index) {
                Some(value) => batch_entry(&value),
                None => Err(AxCode::Failure),
            })
            .collect()
    }

    /// How many values an array attribute holds, without copying them.
    pub(crate) fn count(&self, attribute: &'static str) -> Result<u32, AxCode> {
        let name = CFString::from_static_str(attribute);
        let mut count: CFIndex = 0;
        // SAFETY: `count` is writable for the synchronous call.
        AxCode::check(unsafe {
            self.0
                .attribute_value_count(&name, NonNull::from(&mut count))
        })?;
        Ok(u32::try_from(count).unwrap_or(u32::MAX))
    }

    pub(crate) fn settable(&self, attribute: &'static str) -> Result<bool, AxCode> {
        let name = CFString::from_static_str(attribute);
        let mut settable = 0u8;
        // SAFETY: `settable` is a writable Boolean for the synchronous call.
        AxCode::check(unsafe {
            self.0
                .is_attribute_settable(&name, NonNull::from(&mut settable).cast())
        })?;
        Ok(settable != 0)
    }

    pub(crate) fn write_text(&self, attribute: &'static str, text: &str) -> Result<(), AxCode> {
        self.write(attribute, &CFString::from_str(text))
    }

    pub(crate) fn write_bool(&self, attribute: &'static str, value: bool) -> Result<(), AxCode> {
        self.write(attribute, CFBoolean::new(value))
    }

    pub(crate) fn write_range(
        &self,
        attribute: &'static str,
        location: i64,
        length: i64,
    ) -> Result<(), AxCode> {
        let range = CFRange {
            location: isize::try_from(location).map_err(|_| AxCode::IllegalArgument)?,
            length: isize::try_from(length).map_err(|_| AxCode::IllegalArgument)?,
        };
        // SAFETY: `range` is a live CFRange for the CFRange AXValue type.
        let value =
            unsafe { AXValue::new(AXValueType::CFRange, NonNull::from(&range).cast::<c_void>()) }
                .ok_or(AxCode::Failure)?;
        self.write(attribute, &value)
    }

    fn write(&self, attribute: &'static str, value: &CFType) -> Result<(), AxCode> {
        let name = CFString::from_static_str(attribute);
        // SAFETY: name and value are live CF objects for the call.
        AxCode::check(unsafe { self.0.set_attribute_value(&name, value) })
    }

    /// The actions the element performs, as the app names them.
    pub(crate) fn actions(&self) -> Result<Vec<String>, AxCode> {
        let mut out: *const CFArray = ptr::null();
        // SAFETY: `out` is writable and receives a +1 CFArray on success.
        AxCode::check(unsafe { self.0.copy_action_names(NonNull::from(&mut out)) })?;
        let Some(array) = retained(out) else {
            return Ok(Vec::new());
        };
        // SAFETY: action names are CFStrings.
        let names = unsafe { CFRetained::cast_unchecked::<CFArray<CFString>>(array) };
        Ok(names.iter().map(|name| name.to_string()).collect())
    }

    pub(crate) fn perform(&self, action: &'static str) -> Result<(), AxCode> {
        let name = CFString::from_static_str(action);
        // SAFETY: the retained element and the name outlive the call.
        AxCode::check(unsafe { self.0.perform_action(&name) })
    }

    /// The window server id of this window element.
    pub(crate) fn window_id(&self, get: WindowIdFn) -> Option<u32> {
        let mut id = 0u32;
        let element: *const AXUIElement = &raw const *self.0;
        // SAFETY: `get` has `_AXUIElementGetWindow`'s ABI; the element is
        // retained and `id` writable for the synchronous call.
        (unsafe { get(element, &raw mut id) } == 0 && id != 0).then_some(id)
    }
}

/// Takes a +1 CF object a copy call stored, `None` for null.
fn retained<T: Type>(pointer: *const T) -> Option<CFRetained<T>> {
    // SAFETY: AX copy calls return their output at +1.
    NonNull::new(pointer.cast_mut()).map(|pointer| unsafe { CFRetained::from_raw(pointer) })
}

/// One entry of a batched read: `CFNull` for no value, an `AXValue` of type
/// `AXError` for the attribute's error.
fn batch_entry(value: &CFType) -> Read {
    if value.downcast_ref::<CFNull>().is_some() {
        return Ok(None);
    }
    if let Some(ax) = value.downcast_ref::<AXValue>() {
        // SAFETY: reading a live AXValue's type has no preconditions.
        if unsafe { ax.r#type() } == AXValueType::AXError {
            let mut error = AXError::Failure;
            // SAFETY: an AXError AXValue holds exactly one AXError.
            unsafe { ax.value(AXValueType::AXError, NonNull::from(&mut error).cast()) };
            return match AxCode::check(error) {
                Ok(()) | Err(AxCode::NoValue) => Ok(None),
                Err(code) => Err(code),
            };
        }
    }
    Ok(decode(value))
}

fn decode(value: &CFType) -> Option<Value> {
    if value.downcast_ref::<CFNull>().is_some() {
        return None;
    }
    if let Some(text) = value.downcast_ref::<CFString>() {
        return Some(Value::Text(text.to_string()));
    }
    if let Some(boolean) = value.downcast_ref::<CFBoolean>() {
        return Some(Value::Bool(boolean.as_bool()));
    }
    if let Some(number) = value.downcast_ref::<CFNumber>() {
        return Some(number_value(number));
    }
    if let Some(element) = value.downcast_ref::<AXUIElement>() {
        return Some(Value::Element(AxHandle(element.retain())));
    }
    if let Some(ax) = value.downcast_ref::<AXValue>() {
        return Some(ax_value(ax));
    }
    if let Some(url) = value.downcast_ref::<CFURL>() {
        return Some(Value::Url(url.string().to_string()));
    }
    if let Some(array) = value.downcast_ref::<CFArray>() {
        // SAFETY: AX arrays hold CF objects.
        let array = unsafe { &*ptr::from_ref(array).cast::<CFArray<CFType>>() };
        return Some(Value::Elements(
            array
                .iter()
                .filter_map(|item| item.downcast::<AXUIElement>().ok().map(AxHandle))
                .collect(),
        ));
    }
    Some(Value::Other)
}

fn number_value(number: &CFNumber) -> Value {
    if !number.is_float_type() {
        return number.as_i64().map_or(Value::Other, Value::Int);
    }
    if number.byte_size() <= 4 {
        number.as_f32().map_or(Value::Other, |value| {
            Value::Float(f64::from(value), Width::Single)
        })
    } else {
        number
            .as_f64()
            .map_or(Value::Other, |value| Value::Float(value, Width::Double))
    }
}

fn ax_value(value: &AXValue) -> Value {
    // SAFETY: reading a live AXValue's type has no preconditions.
    let kind = unsafe { value.r#type() };
    match kind {
        AXValueType::CGPoint => {
            let mut point = CGPoint { x: 0.0, y: 0.0 };
            // SAFETY: the output is a live CGPoint for the CGPoint type.
            if unsafe { value.value(kind, NonNull::from(&mut point).cast()) } {
                Value::Point {
                    x: point.x,
                    y: point.y,
                }
            } else {
                Value::Other
            }
        }
        AXValueType::CGSize => {
            let mut size = CGSize {
                width: 0.0,
                height: 0.0,
            };
            // SAFETY: the output is a live CGSize for the CGSize type.
            if unsafe { value.value(kind, NonNull::from(&mut size).cast()) } {
                Value::Size {
                    width: size.width,
                    height: size.height,
                }
            } else {
                Value::Other
            }
        }
        AXValueType::CFRange => {
            let mut range = CFRange {
                location: 0,
                length: 0,
            };
            // SAFETY: the output is a live CFRange for the CFRange type.
            let read = unsafe { value.value(kind, NonNull::from(&mut range).cast()) };
            match (
                read,
                i64::try_from(range.location),
                i64::try_from(range.length),
            ) {
                (true, Ok(location), Ok(length)) => Value::Range { location, length },
                (true | false, _, _) => Value::Other,
            }
        }
        _ => Value::Other,
    }
}
