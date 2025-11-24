use anyhow::Result;
use cranelift_codegen::{
    Context, isa,
    settings::{self, Configurable},
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_reader::parse_functions;
use std::collections::HashMap;
use std::ffi::CStr;
use std::os::raw::c_char;
use std::slice;

pub struct CraneliftBackend {
    module: JITModule,
    functions: HashMap<String, FuncId>,
}

impl CraneliftBackend {
    pub fn new(target: &str) -> Result<Self> {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false")?;
        flag_builder.set("is_pic", "false")?;

        let isa_builder = isa::lookup_by_name(target)?;
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();

        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let module = JITModule::new(builder);

        Ok(CraneliftBackend {
            module,
            functions: HashMap::new(),
        })
    }

    pub fn compile_module(&mut self, clif_text: &str) -> Result<Vec<String>> {
        let funcs = parse_functions(clif_text)?;

        let mut compiled_names = Vec::new();
        for func in funcs {
            let name = func.name.to_string();
            let sig = func.signature.clone();

            let id = self.module.declare_function(&name, Linkage::Export, &sig)?;
            let mut ctx = Context::for_function(func);
            self.module.define_function(id, &mut ctx)?;
            self.module.clear_context(&mut ctx);

            self.functions.insert(name.clone(), id);
            compiled_names.push(name.clone());
        }

        self.module.finalize_definitions()?;
        Ok(compiled_names)
    }

    pub fn get_function_ptr(&self, name: &str) -> Option<*const ()> {
        self.functions
            .get(name)
            .map(|&id| self.module.get_finalized_function(id) as *const ())
    }

    pub fn get_all_function_names(&self) -> Vec<String> {
        let names: Vec<String> = self.functions.keys().cloned().collect();
        names
    }
}

pub struct BackendHandle {
    backend: CraneliftBackend,
}

#[unsafe(no_mangle)]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn cranelift_compile(
    clif_text: *const u8,
    clif_len: usize,
    target: *const u8,
    target_len: usize,
) -> *mut BackendHandle {
    if clif_text.is_null() || target.is_null() {
        return std::ptr::null_mut();
    }

    let clif_bytes = slice::from_raw_parts(clif_text, clif_len);
    let clif_str = match std::str::from_utf8(clif_bytes) {
        Ok(s) => s,
        Err(_) => return std::ptr::null_mut(),
    };

    let target_bytes = slice::from_raw_parts(target, target_len);
    let target_str = match std::str::from_utf8(target_bytes) {
        Ok(s) => s,
        Err(_) => return std::ptr::null_mut(),
    };

    let mut backend = match CraneliftBackend::new(target_str) {
        Ok(b) => b,
        Err(_) => return std::ptr::null_mut(),
    };

    match backend.compile_module(clif_str) {
        Ok(_) => Box::into_raw(Box::new(BackendHandle { backend })),
        Err(_) => std::ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn cranelift_get_function(
    handle: *const BackendHandle,
    func_name: *const c_char,
) -> *const () {
    if handle.is_null() || func_name.is_null() {
        return std::ptr::null();
    }

    let handle = &*handle;
    let name_cstr = CStr::from_ptr(func_name);
    let name = match name_cstr.to_str() {
        Ok(s) => s,
        Err(_) => return std::ptr::null(),
    };

    handle
        .backend
        .get_function_ptr(name)
        .unwrap_or(std::ptr::null())
}

#[unsafe(no_mangle)]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn cranelift_function_count(handle: *const BackendHandle) -> usize {
    if handle.is_null() {
        return 0;
    }

    let handle = unsafe { &*handle };
    handle.backend.functions.len()
}

#[unsafe(no_mangle)]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn cranelift_get_function_name(
    handle: *const BackendHandle,
    index: usize,
    out_buffer: *mut u8,
    buffer_len: usize,
) -> i32 {
    if handle.is_null() || out_buffer.is_null() || buffer_len == 0 {
        return 0;
    }

    let handle = unsafe { &*handle };
    let names = handle.backend.get_all_function_names();

    if index >= names.len() {
        return 0;
    }

    let name = &names[index];
    let name_bytes = name.as_bytes();

    if name_bytes.len() + 1 > buffer_len {
        return 0;
    }

    let out_slice = unsafe { slice::from_raw_parts_mut(out_buffer, buffer_len) };
    out_slice[..name_bytes.len()].copy_from_slice(name_bytes);
    out_slice[name_bytes.len()] = 0;

    1
}

#[unsafe(no_mangle)]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn cranelift_free(handle: *mut BackendHandle) {
    if !handle.is_null() {
        unsafe { drop(Box::from_raw(handle)) };
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelift_last_error() -> *const c_char {
    c"Check return values".as_ptr() as *const c_char
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    const ARCH: &str = std::env::consts::ARCH;

    #[test]
    fn test_basic_compilation() {
        let clif = r#"
function u0:0(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 1
    v2 = iadd v0, v1
    return v2
}
"#;

        let clif_cstring = CString::new(clif).unwrap();
        let target_cstring = CString::new(ARCH).unwrap();

        unsafe {
            let handle = cranelift_compile(
                clif_cstring.as_ptr() as *const u8,
                clif.len(),
                target_cstring.as_ptr() as *const u8,
                target_cstring.as_bytes().len(),
            );

            assert!(!handle.is_null());

            let func_name = CString::new("u0:0").unwrap();
            let func_ptr = cranelift_get_function(handle, func_name.as_ptr());

            assert!(!func_ptr.is_null());

            type FnType = extern "C" fn(i64) -> i64;
            let f: FnType = std::mem::transmute(func_ptr);
            let result = f(41);
            assert_eq!(result, 42);

            cranelift_free(handle);
        }
    }

    #[test]
    fn test_multiple_functions() {
        let clif = r#"
function u0:0(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 1
    v2 = iadd v0, v1
    return v2
}

function u0:1(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 2
    v2 = imul v0, v1
    return v2
}
"#;

        let clif_cstring = CString::new(clif).unwrap();
        let target_cstring = CString::new(ARCH).unwrap();

        unsafe {
            let handle = cranelift_compile(
                clif_cstring.as_ptr() as *const u8,
                clif.len(),
                target_cstring.as_ptr() as *const u8,
                target_cstring.as_bytes().len(),
            );

            assert!(!handle.is_null());
            assert_eq!(cranelift_function_count(handle), 2);

            let func1_name = CString::new("u0:0").unwrap();
            let func1_ptr = cranelift_get_function(handle, func1_name.as_ptr());
            assert!(!func1_ptr.is_null());

            type FnType = extern "C" fn(i64) -> i64;
            let f1: FnType = std::mem::transmute(func1_ptr);
            assert_eq!(f1(10), 11);

            let func2_name = CString::new("u0:1").unwrap();
            let func2_ptr = cranelift_get_function(handle, func2_name.as_ptr());
            assert!(!func2_ptr.is_null());

            let f2: FnType = std::mem::transmute(func2_ptr);
            assert_eq!(f2(10), 20);

            cranelift_free(handle);
        }
    }
}
