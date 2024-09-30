variable "google_region" {
  type        = string
  description = "The region on GCP"
  default     = "us-east1"
}

variable "google_zone" {
  type        = string
  description = "The zone on GCP"
  default     = "us-east1-b"
}

variable "google_service_account" {
  type        = string
  description = "The service account to use for deploying services"
}

variable "google_service_credentials_json_file" {
  type        = string
  description = "The credentials of the GCP service account"
}

variable "terraform_backend_bucket" {
  type = string
  description = "The bucket to use to store terraform's state"
  default = "peras_infra"
}

variable "terraform_backend_prefix" {
  type = string
  description = "The prefix path to store terraform's state at"
  default = "terraform/peras/state"
}

locals {
  google_service_credentials_json_file_decoded = jsondecode(file(var.google_service_credentials_json_file))
  google_service_account_private_key           = local.google_service_credentials_json_file_decoded.private_key
  google_project_id                            = local.google_service_credentials_json_file_decoded.project_id
  terraform_backend_prefix = var.terraform_backend_prefix
  terraform_backend_bucket = var.terraform_backend_bucket
}
